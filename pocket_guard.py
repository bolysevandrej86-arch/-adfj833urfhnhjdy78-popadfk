"""Pocket Guard — подтверждение отправки медиа/текста и защита ссылок.

Teaches in practice: on_send_message_hook with HookStrategy.CANCEL + resend,
Xposed hooking of Browser.openUrl (hook_all_methods), AlertDialogBuilder,
settings (Switch/Input/Text), multi-account scoping (account= everywhere).

See: https://plugins.exteragram.app/docs
"""

import json
import threading
import time
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urlencode, urlparse

from base_plugin import (  # pyright: ignore[reportMissingImports]
    BasePlugin,
    HookResult,
    HookStrategy,
    MenuItemData,
    MenuItemType,
    MethodHook,
)
from ui.settings import (  # pyright: ignore[reportMissingImports]
    Divider,
    Header,
    Input,
    Switch,
    Text,
)
from ui.alert import AlertDialogBuilder  # pyright: ignore[reportMissingImports]
from ui.bulletin import BulletinHelper  # pyright: ignore[reportMissingImports]
from android_utils import log, run_on_ui_thread  # pyright: ignore[reportMissingImports]
from client_utils import (  # pyright: ignore[reportMissingImports]
    get_last_fragment,
    get_messages_controller,
    get_send_messages_helper,
    run_on_queue,
    send_request,
)
from hook_utils import find_class  # pyright: ignore[reportMissingImports]
from android.net import Uri  # pyright: ignore[reportMissingImports]
from java.net import HttpURLConnection, URL  # pyright: ignore[reportMissingImports]
from java.util import Scanner  # pyright: ignore[reportMissingImports]

try:
    from org.telegram.messenger import Browser  # pyright: ignore[reportMissingImports]
except ImportError:
    Browser = None

__id__ = "pocket_guard"
__name__ = "Pocket Guard"
__description__ = (
    "🛡 Защита от «телефона в кармане»: отправка медиа и текста — только после подтверждения.\n\n"
    "🔗 Ссылки открываются только после проверки адреса, с проверкой по блок-листам "
    "(Google Safe Browsing, URLhaus) и режимом анонимного чтения (IP не светится)."
)
__author__ = "ZCode"
__version__ = "1.1.0"
__icon__ = "exteraPlugins/1"
__app_version__ = ">=12.5.1"
__sdk_version__ = ">=1.4.5.0"

DEFAULT_ANON_PREFIX = "https://r.jina.ai/"
DEFAULT_WHITELIST = "telegram.org,t.me,core.telegram.org,graph.telegram.org,extera.app,exteragram.app"

SAFE_BROWSING_ENDPOINT = "https://safebrowsing.googleapis.com/v4/threatMatches:find"
URLHAUS_URL_ENDPOINT = "https://urlhaus-api.abuse.ch/v1/url/"
URLHAUS_HOST_ENDPOINT = "https://urlhaus-api.abuse.ch/v1/host/"

# Сколько секунд держать вердикт проверки ссылки в кэше.
VERDICT_CACHE_TTL = 3600.0
# Неудачная проверка (сеть/сервис) кэшируется ненадолго, чтобы не кэшировать «чисто».
FAILURE_CACHE_TTL = 30.0
# Таймауты HTTP-запросов к блок-листам.
HTTP_TIMEOUT_MS = 4000

# Сторожевой вердикт: проверка не удалась (отличать от «чисто»).
CHECK_FAILED = {"failed": True}

# Сколько секунд ждать новые части альбома / серию отправок в тот же чат.
ALBUM_MERGE_WINDOW = 3.0
# Сколько секунд висит неподтверждённая отправка, прежде чем слот освобождается.
PENDING_TTL = 120.0
# Окно, в которое повторный вход хука с теми же параметрами пропускается (повторная отправка).
RESEND_ALLOW_WINDOW = 5.0
# Максимум ожидающих подтверждения пачек (разные чаты подряд).
MAX_QUEUE = 10


def _safe_str(v: Any) -> str:
    try:
        return str(v)
    except Exception:
        return ""


def _http_post_text(url_str: str, body: str, content_type: str) -> Optional[str]:
    """POST через HttpURLConnection (проверенный в Chaquopy путь), тело ответа строкой."""
    conn: Optional[HttpURLConnection] = None
    try:
        conn = URL(url_str).openConnection()
        conn.setRequestMethod("POST")
        conn.setConnectTimeout(HTTP_TIMEOUT_MS)
        conn.setReadTimeout(HTTP_TIMEOUT_MS)
        conn.setDoOutput(True)
        conn.setRequestProperty("Content-Type", content_type)
        out = conn.getOutputStream()
        out.write(body.encode("utf-8"))
        out.flush()
        out.close()
        code = conn.getResponseCode()
        if code != 200:
            log(f"Pocket Guard: HTTP {code} from {url_str.split('?')[0]}")
            return None
        scanner = Scanner(conn.getInputStream(), "UTF-8").useDelimiter("\\A")
        try:
            return scanner.next() if scanner.hasNext() else ""
        finally:
            try:
                scanner.close()
            except Exception:
                pass
    except Exception as e:
        log(f"Pocket Guard HTTP error ({url_str.split('?')[0]}): {e}")
        return None
    finally:
        if conn is not None:
            try:
                conn.disconnect()
            except Exception:
                pass


class _LinkOpenHook(MethodHook):
    """Перехватывает Browser.openUrl(...) — все перегрузки."""

    def __init__(self, plugin: "PocketGuardPlugin"):
        self.plugin = plugin

    def before_hooked_method(self, param):
        self.plugin.handle_link_open(param)


class PocketGuardPlugin(BasePlugin):
    # Дефолты уровня класса: unload может прийти раньше/вместо load.
    _lock = threading.Lock()
    _link_lock = threading.Lock()
    _verdict_lock = threading.Lock()
    _pending: Optional[Dict[str, Any]] = None
    _queue: List[Dict[str, Any]] = []
    _bypass = False
    _allowed_ids = set()
    _allow_fp: Optional[Tuple] = None
    _allow_until = 0.0
    _snooze_until = 0.0
    _link_unhooks: List[Any] = []
    _verdict_cache: Dict[str, Tuple[Any, float]] = {}
    _link_inflight = set()
    _active_link: Optional[Tuple[str, Any]] = None

    def on_plugin_load(self):
        self._pending = None
        self._queue = []
        self._bypass = False
        self._allowed_ids = set()
        self._allow_fp = None
        self._allow_until = 0.0
        self._snooze_until = 0.0
        self._link_unhooks = []
        with self._verdict_lock:
            self._verdict_cache = {}
            self._link_inflight = set()
            self._active_link = None

        self.add_on_send_message_hook()

        if self.get_setting("link_shield", True):
            self._install_link_hook()

        self.add_menu_item(
            MenuItemData(
                menu_type=MenuItemType.DRAWER_MENU,
                text="Pocket Guard: пауза подтверждений (1 час)",
                on_click=self._on_snooze_click,
                icon="msg_info",
            )
        )
        log("Pocket Guard loaded")

    def on_plugin_unload(self):
        # Хуки снимаются автоматически; чистим состояние.
        with self._lock:
            self._pending = None
            self._queue = []
        self._uninstall_link_hook()

    # ------------------------------------------------------------------
    # Настройки
    # ------------------------------------------------------------------

    def create_settings(self) -> List[Any]:
        return [
            Header(text="Защита отправок"),
            Switch(
                key="confirm_media",
                text="Подтверждать медиа",
                default=True,
                subtext="Фото, видео, голосовые, кружки, файлы, стикеры, локации",
                icon="msg_settings",
            ),
            Switch(
                key="confirm_text",
                text="Подтверждать текст",
                default=False,
                subtext="Спрашивать и перед обычными сообщениями",
                icon="msg_text",
            ),
            Divider(text="Защита ссылок (анти-фишинг и приватность)"),
            Switch(
                key="link_shield",
                text="Проверять ссылки перед открытием",
                default=True,
                subtext="Показывает реальный адрес, умеет открывать анонимно",
                icon="msg_info",
                on_change=self._on_link_shield_change,
            ),
            Switch(
                key="urlhaus_check",
                text="URLhaus (abuse.ch)",
                default=True,
                subtext="База распространителей малвари, работает без ключа",
                icon="msg_list",
            ),
            Switch(
                key="sb_check",
                text="Google Safe Browsing",
                default=True,
                subtext="Фишинг и вредоносные сайты; нужен бесплатный API-ключ",
                icon="msg_settings",
            ),
            Input(
                key="sb_api_key",
                text="API-ключ Safe Browsing",
                default="",
                subtext="console.cloud.google.com → Safe Browsing API → ключ",
                icon="msg_edit",
            ),
            Input(
                key="anon_prefix",
                text="Префикс анонимного чтения",
                default=DEFAULT_ANON_PREFIX,
                subtext="Страница загрузится через этот сервис, ваш IP сайт не увидит",
                icon="msg_edit",
            ),
            Input(
                key="link_whitelist",
                text="Белый список доменов",
                default=DEFAULT_WHITELIST,
                subtext="Через запятую; эти домены открываются без вопросов",
                icon="msg_edit",
            ),
            Text(
                text="Как это работает",
                subtext="Нажмите для справки",
                icon="msg_arrow_forward",
                on_click=self._show_help,
            ),
        ]

    def _show_help(self, view):
        self._show_dialog(
            title="Pocket Guard — справка",
            message=(
                "1. Медиа (и по желанию текст) не отправляются сразу: сначала диалог "
                "«Отправить?». Это защита от случайных отправок, когда телефон в кармане.\n\n"
                "2. Ссылки из сообщений не открываются, пока вы не подтвердите: "
                "[Открыть] — как обычно, [Анонимно] — через прокси-ридер "
                "(по умолчанию r.jina.ai: страницу скачивает его сервер, ваш IP сайт не видит), "
                "[Отмена] — не открывать. Домены из белого списка открываются сразу.\n\n"
                "3. Перед показом диалога ссылка проверяется по блок-листам: URLhaus "
                "(малварь, без ключа) и Google Safe Browsing (фишинг; ключ берётся "
                "бесплатно в console.cloud.google.com). Опасные ссылки показывают "
                "красное предупреждение.\n\n"
                "4. В боковом меню есть пункт «пауза подтверждений на 1 час» — "
                "для активного общения.\n\n"
                "Защищены обычные чаты, группы и каналы. Секретные чаты, "
                "мини-приложения (Web Apps) и вложения ботов не перехватываются."
            ),
        )

    # ------------------------------------------------------------------
    # Хук исходящих сообщений
    # ------------------------------------------------------------------

    def on_send_message_hook(self, account: int, params: Any) -> HookResult:
        try:
            if self._bypass:
                return HookResult()

            # Повторная отправка после подтверждения: пропускаем.
            now = time.time()
            if id(params) in self._allowed_ids:
                self._allowed_ids.discard(id(params))
                return HookResult()
            if self._allow_fp is not None and now < self._allow_until:
                if self._allow_fp == self._fingerprint(account, params):
                    return HookResult()

            if now < self._snooze_until:
                return HookResult()

            kind = self._classify_send(params)
            if kind == "media" and not self.get_setting("confirm_media", True):
                kind = None
            if kind == "text" and not self.get_setting("confirm_text", False):
                kind = None
            if kind is None:
                return HookResult()

            fp = self._fingerprint(account, params)
            with self._lock:
                if (
                    self._pending is not None
                    and now >= self._pending["until"]
                    and not self._pending.get("shown")
                ):
                    # Протухла пачка, чей диалог ещё даже не открылся.
                    self._pending = None
                    BulletinHelper.show_error(
                        "Pocket Guard: отправка отменена (таймаут)", get_last_fragment()
                    )
                if (
                    self._pending is not None
                    and self._pending["fp"] == fp
                    and now - self._pending["ts"] <= ALBUM_MERGE_WINDOW
                ):
                    # Альбом / серия отправок в тот же чат: копим в одну пачку.
                    self._pending["items"].append(params)
                    self._pending["ts"] = now
                    return HookResult(strategy=HookStrategy.CANCEL)

                pending = {
                    "items": [params],
                    "account": account,
                    "kind": kind,
                    "label": self._media_label(params) if kind == "media" else "сообщение",
                    "chat": self._chat_label(account, params),
                    "preview": self._preview(params),
                    "fp": fp,
                    "ts": now,
                    "until": now + PENDING_TTL,
                }
                if self._pending is not None:
                    # Уже ждёт решение по другой отправке — в очередь.
                    if len(self._queue) < MAX_QUEUE:
                        self._queue.append(pending)
                    else:
                        log("Pocket Guard: queue overflow, dropping pending send")
                        BulletinHelper.show_error(
                            "Pocket Guard: слишком много ожидающих отправок, лишняя отменена",
                            get_last_fragment(),
                        )
                    return HookResult(strategy=HookStrategy.CANCEL)
                self._pending = pending

            run_on_ui_thread(self._show_send_dialog)
            return HookResult(strategy=HookStrategy.CANCEL)
        except Exception as e:
            log(f"Pocket Guard on_send_message_hook error: {e}")
            return HookResult()

    def _show_send_dialog(self):
        with self._lock:
            pending = self._pending
        if pending is None:
            return

        frag = get_last_fragment()
        activity = frag.getParentActivity() if frag else None
        if not activity:
            with self._lock:
                if self._pending is pending:
                    self._pending = None
            BulletinHelper.show_error("Pocket Guard: диалог недоступен, отправка отменена", frag)
            self._resolve_next()
            return

        with self._lock:
            if self._pending is not pending:
                return
            pending["shown"] = True

        n = len(pending["items"])
        if pending["kind"] == "media":
            text = "Отправить {}{} в «{}»?".format(
                pending["label"], f" ({n} шт.)" if n > 1 else "", pending["chat"]
            )
        else:
            text = "Отправить сообщение{} в «{}»?".format(
                f" ({n} шт.)" if n > 1 else "", pending["chat"]
            )
            if pending["preview"]:
                text += f"\n\n«{pending['preview']}»"

        try:
            builder = AlertDialogBuilder(activity)
            builder.set_title("Подтверждение отправки")
            builder.set_message(text)
            builder.set_positive_button("Отправить", lambda bld, w: self._confirm_send(bld, pending))
            builder.set_negative_button("Отмена", lambda bld, w: self._drop_send(bld, pending))
            builder.create()
            builder.set_cancelable(True)
            builder.set_on_cancel_listener(lambda bld: self._drop_send(bld, pending))
            builder.show()
        except Exception as e:
            log(f"Pocket Guard dialog error: {e}")
            self._drop_send(None, pending)

    def _confirm_send(self, bld, pending):
        if bld is not None:
            try:
                bld.dismiss()
            except Exception:
                pass
        with self._lock:
            if self._pending is not pending:
                return
            items = list(pending["items"])
            account = pending["account"]
            self._pending = None
        self._resend_items(account, items)
        self._resolve_next()

    def _drop_send(self, bld, pending):
        if bld is not None:
            try:
                bld.dismiss()
            except Exception:
                pass
        advance = False
        with self._lock:
            if self._pending is pending:
                self._pending = None
                advance = True
        if advance:
            self._resolve_next()

    def _resolve_next(self):
        with self._lock:
            now = time.time()
            dropped = 0
            while self._queue and now >= self._queue[0]["until"]:
                self._queue.pop(0)
                dropped += 1
            if dropped:
                BulletinHelper.show_error(
                    f"Pocket Guard: {dropped} ожидающих отправок устарели и отменены",
                    get_last_fragment(),
                )
            if not self._queue:
                return
            self._pending = self._queue.pop(0)
        run_on_ui_thread(self._show_send_dialog)

    def _resend_items(self, account: int, items: List[Any]):
        self._bypass = True
        ok_any = False
        try:
            for p in items:
                self._allowed_ids.add(id(p))
                try:
                    ok = self._resend_one(p, account)
                except Exception as e:
                    ok = False
                    log(f"Pocket Guard resend error: {e}")
                if ok:
                    ok_any = True
                else:
                    self._allowed_ids.discard(id(p))
            # Короткое окно на случай асинхронного повторного входа хука.
            if ok_any and items:
                self._allow_fp = self._fingerprint(account, items[-1])
                self._allow_until = time.time() + RESEND_ALLOW_WINDOW
        finally:
            self._bypass = False
            for p in items:
                self._allowed_ids.discard(id(p))

    def _resend_one(self, params: Any, account: int) -> bool:
        name = type(params).__name__
        if not name.startswith("TL_"):
            # Высокоуровневые параметры (SendMessagesHelper.SendMessageParams).
            try:
                helper = get_send_messages_helper(account)
                helper.sendMessage(params)
                return True
            except Exception as e:
                log(f"Pocket Guard sendMessage via helper failed: {e}")
        # Фолбэк: отправить как сырой TL-запрос.
        def _on_sent(resp, err):
            if err is not None:
                log(f"Pocket Guard server rejected send: {err}")

        try:
            send_request(params, _on_sent, account=account)
            return True
        except Exception as e:
            log(f"Pocket Guard send_request failed: {e}")
            return False

    # ------------------------------------------------------------------
    # Классификация отправок
    # ------------------------------------------------------------------

    def _classify_send(self, params: Any) -> Optional[str]:
        """Возвращает 'media' | 'text' | None."""
        name = type(params).__name__
        if name in ("TL_messages_sendMedia", "TL_messages_sendMultiMedia"):
            return "media"
        if name == "TL_messages_sendMessage":
            msg = getattr(params, "message", None)
            return "text" if isinstance(msg, str) and msg.strip() else None
        # Высокоуровневые параметры: проверяем атрибуты медиа.
        for attr in ("photo", "document", "video", "audio", "voice", "inputMedia", "media"):
            try:
                if getattr(params, attr, None):
                    return "media"
            except Exception:
                pass
        try:
            if getattr(params, "path", None):
                return "media"
        except Exception:
            pass
        msg = getattr(params, "message", None)
        if isinstance(msg, str) and msg.strip():
            return "text"
        return None

    def _media_label(self, params: Any) -> str:
        name = type(params).__name__
        if name == "TL_messages_sendMultiMedia":
            return "альбом"
        try:
            photo = getattr(params, "photo", None)
            if photo is not None:
                return "фото"
            doc = getattr(params, "document", None)
            if doc is not None:
                for a in getattr(doc, "attributes", []) or []:
                    n = type(a).__name__
                    if n == "TL_documentAttributeVoice":
                        return "голосовое сообщение"
                    if n == "TL_documentAttributeVideo":
                        if getattr(a, "round_message", False):
                            return "видеосообщение"
                        return "видео"
                    if n == "TL_documentAttributeSticker":
                        return "стикер"
                    if n == "TL_documentAttributeAnimated":
                        return "GIF"
                if getattr(doc, "voice", False):
                    return "голосовое сообщение"
                return "файл"
            media = getattr(params, "media", None)
            if media is not None:
                mn = type(media).__name__
                if "Photo" in mn:
                    return "фото"
                if "Geo" in mn:
                    return "геолокацию"
                if "Contact" in mn:
                    return "контакт"
                if "Poll" in mn:
                    return "опрос"
        except Exception:
            pass
        return "медиа"

    def _preview(self, params: Any) -> str:
        try:
            msg = getattr(params, "message", None) or getattr(params, "caption", None) or ""
            if isinstance(msg, str) and msg.strip():
                return msg.strip().replace("\n", " ")[:80]
        except Exception:
            pass
        return ""

    def _peer_dialog_id(self, params: Any) -> Optional[int]:
        try:
            peer = getattr(params, "peer", None)
            if peer is None:
                return None
            if isinstance(peer, int):
                return peer
            n = type(peer).__name__
            if n == "TL_peerUser":
                return int(getattr(peer, "user_id", 0) or 0)
            if n == "TL_peerChat":
                return -int(getattr(peer, "chat_id", 0) or 0)
            if n == "TL_peerChannel":
                return -(1000000000000 + int(getattr(peer, "channel_id", 0) or 0))
        except Exception:
            pass
        return None

    def _fingerprint(self, account: int, params: Any) -> Tuple:
        return (account, self._peer_dialog_id(params), type(params).__name__)

    def _chat_label(self, account: int, params: Any) -> str:
        did = self._peer_dialog_id(params)
        if did is None:
            return "этот чат"
        try:
            mc = get_messages_controller(account)
            if did > 0:
                u = mc.getUser(int(did))
                if u is not None:
                    name = ((getattr(u, "first_name", "") or "") + " " + (getattr(u, "last_name", "") or "")).strip()
                    return name or "пользователь"
            else:
                cid = -int(did)
                if cid >= 1000000000000:
                    cid -= 1000000000000
                c = mc.getChat(int(cid))
                if c is not None:
                    return _safe_str(getattr(c, "title", None)) or "чат"
        except Exception:
            pass
        return "этот чат"

    # ------------------------------------------------------------------
    # Защита ссылок (Xposed-хук Browser.openUrl)
    # ------------------------------------------------------------------

    def _install_link_hook(self):
        with self._link_lock:
            if self._link_unhooks or Browser is None:
                return
            try:
                browser_class = find_class("org.telegram.messenger.Browser")
                unhooks = self.hook_all_methods(browser_class, "openUrl", _LinkOpenHook(self))
                self._link_unhooks = list(unhooks or [])
                log(f"Pocket Guard: link shield active ({len(self._link_unhooks)} openUrl overloads)")
            except Exception as e:
                self._link_unhooks = []
                log(f"Pocket Guard: link hook install failed: {e}")

    def _uninstall_link_hook(self):
        with self._link_lock:
            for u in self._link_unhooks:
                try:
                    self.unhook_method(u)
                except Exception:
                    pass
            self._link_unhooks = []

    def _on_link_shield_change(self, value: bool):
        if value:
            self._install_link_hook()
        else:
            self._uninstall_link_hook()

    def handle_link_open(self, param):
        try:
            if self._bypass:
                return
            if not self.get_setting("link_shield", True):
                return
            if time.time() < self._snooze_until:
                return
            url = self._url_from_args(param.args)
            if not url:
                return
            low = url.lower()
            if not (low.startswith("http://") or low.startswith("https://")):
                return  # tg:// и прочие внутренние схемы не трогаем
            parsed = urlparse(url)
            host = (parsed.hostname or parsed.netloc or "").lower()
            if not host or self._is_whitelisted(host):
                return
            context = param.args[0] if len(param.args) > 0 else None
            param.setResult(None)  # не открываем, пока нет решения
            run_on_ui_thread(lambda: self._start_link_flow(context, url, host))
        except Exception as e:
            log(f"Pocket Guard handle_link_open error: {e}")

    # ------------------------------------------------------------------
    # Проверка ссылок по блок-листам
    # ------------------------------------------------------------------

    def _start_link_flow(self, context, url: str, host: str):
        """Фоновая проверка блок-листов, затем диалог (обычный или красный)."""
        with self._verdict_lock:
            if url in self._link_inflight:
                return  # проверка этого же URL уже идёт, диалог покажет она
            self._link_inflight.add(url)

        def work():
            try:
                verdict = self._check_blocklists(url, host)
            except Exception as e:
                log(f"Pocket Guard blocklist check error: {e}")
                verdict = None
            finally:
                with self._verdict_lock:
                    self._link_inflight.discard(url)
            run_on_ui_thread(lambda: self._show_link_dialog(context, url, host, verdict))

        try:
            run_on_queue(work)
        except Exception as e:
            # Очередь недоступна (например, при выгрузке плагина) — не теряем ссылку.
            with self._verdict_lock:
                self._link_inflight.discard(url)
            log(f"Pocket Guard run_on_queue failed: {e}")
            run_on_ui_thread(lambda: self._show_link_dialog(context, url, host, None))

    def _check_blocklists(self, url: str, host: str) -> Any:
        """None = чисто; dict = красное предупреждение; CHECK_FAILED = сервис недоступен."""
        cache_key = url
        now = time.time()
        with self._verdict_lock:
            cached = self._verdict_cache.get(cache_key)
            if cached is not None and now < cached[1]:
                return cached[0]

        verdict: Optional[Dict[str, str]] = None
        any_failed = False
        if self.get_setting("urlhaus_check", True):
            verdict, ok = self._check_urlhaus(url, host)
            any_failed = any_failed or not ok
        if verdict is None and self.get_setting("sb_check", True):
            api_key = _safe_str(self.get_setting("sb_api_key", "")).strip()
            if api_key:
                verdict, ok = self._check_safe_browsing(url, api_key)
                any_failed = any_failed or not ok

        if verdict is not None:
            result: Any = verdict
            ttl = VERDICT_CACHE_TTL
        elif any_failed:
            result = CHECK_FAILED
            ttl = FAILURE_CACHE_TTL
        else:
            result = None
            ttl = VERDICT_CACHE_TTL
        with self._verdict_lock:
            self._verdict_cache[cache_key] = (result, time.time() + ttl)
        return result

    def _check_safe_browsing(self, url: str, api_key: str) -> Tuple[Optional[Dict[str, str]], bool]:
        """Google Safe Browsing v4 (Lookup API). (None, True) = чисто, (None, False) = сбой."""
        try:
            body = json.dumps(
                {
                    "client": {"clientId": "pocket_guard", "clientVersion": "1.1.0"},
                    "threatInfo": {
                        "threatTypes": [
                            "MALWARE",
                            "SOCIAL_ENGINEERING",
                            "UNWANTED_SOFTWARE",
                            "POTENTIALLY_HARMFUL_APPLICATION",
                        ],
                        "platformTypes": ["ANY_PLATFORM"],
                        "threatEntryTypes": ["URL"],
                        "threatEntries": [{"url": url}],
                    },
                }
            )
            resp = _http_post_text(
                f"{SAFE_BROWSING_ENDPOINT}?key={api_key}", body, "application/json; charset=utf-8"
            )
            if resp is None:
                return (None, False)
            if not resp.strip():
                return (None, True)
            matches = json.loads(resp).get("matches") or []
            if matches:
                m = matches[0]
                return (
                    {
                        "source": "Google Safe Browsing",
                        "type": _safe_str(m.get("threatType")) or "THREAT",
                    },
                    True,
                )
            return (None, True)
        except Exception as e:
            log(f"Pocket Guard Safe Browsing error: {e}")
            return (None, False)

    def _urlhaus_api(self, endpoint: str, params: Dict[str, str]) -> Optional[Dict[str, Any]]:
        resp = _http_post_text(endpoint, urlencode(params), "application/x-www-form-urlencoded")
        if resp is None or not resp.strip():
            return None
        try:
            return json.loads(resp)
        except Exception as e:
            log(f"Pocket Guard URLhaus JSON error: {e}")
            return None

    def _check_urlhaus(self, url: str, host: str) -> Tuple[Optional[Dict[str, str]], bool]:
        """abuse.ch URLhaus: точный URL, затем хост. (None, True) = чисто."""
        data = self._urlhaus_api(URLHAUS_URL_ENDPOINT, {"url": url})
        if data is None:
            return (None, False)
        if data.get("query_status") == "ok":
            threat = _safe_str(data.get("threat")) or "malware"
            return ({"source": "URLhaus (abuse.ch)", "type": threat}, True)
        data = self._urlhaus_api(URLHAUS_HOST_ENDPOINT, {"host": host})
        if data is None:
            return (None, False)
        if data.get("query_status") == "ok":
            return ({"source": "URLhaus (abuse.ch)", "type": "малварь на этом домене"}, True)
        return (None, True)

    def _url_from_args(self, args) -> Optional[str]:
        for a in args or []:
            if a is None:
                continue
            if isinstance(a, str):
                return a
            try:
                if isinstance(a, Uri):
                    return a.toString()
            except Exception:
                pass
        return None

    def _is_whitelisted(self, host: str) -> bool:
        raw = _safe_str(self.get_setting("link_whitelist", DEFAULT_WHITELIST))
        for d in raw.split(","):
            d = d.strip().lower().lstrip(".")
            if d and (host == d or host.endswith("." + d)):
                return True
        return False

    def _show_link_dialog(self, context, url: str, host: str, verdict: Any = None):
        dangerous = verdict is not None and not verdict.get("failed", False)
        frag = get_last_fragment()
        activity = frag.getParentActivity() if frag else None
        if not activity:
            if dangerous:
                # Показать предупреждение негде — опасную ссылку молча не открываем.
                BulletinHelper.show_error("Pocket Guard: опасная ссылка, открытие отменено", frag)
                return
            # Обычную ссылку открываем как обычно, чтобы не ломать ссылки.
            self._reopen(context, url)
            return

        with self._verdict_lock:
            active = self._active_link
            if active is not None and active[0] == url:
                return  # диалог для этой ссылки уже открыт

        def do_open(bld, which):
            if bld is not None:
                bld.dismiss()
            self._reopen(context, url)

        def do_anon(bld, which):
            if bld is not None:
                bld.dismiss()
            prefix = _safe_str(self.get_setting("anon_prefix", DEFAULT_ANON_PREFIX)).strip()
            if not prefix:
                prefix = DEFAULT_ANON_PREFIX
            self._reopen(context, prefix + url)

        try:
            builder = AlertDialogBuilder(activity)
            if dangerous:
                builder.set_title("⚠️ ОПАСНАЯ ССЫЛКА")
                builder.set_message(
                    f"{host}\n\n{url}\n\n"
                    f"🚨 {verdict.get('source', '')}: {verdict.get('type', 'угроза')}\n\n"
                    "Не открывайте файлы и не вводите здесь пароли, коды или данные карт!"
                )
                builder.set_positive_button("Всё равно открыть", do_open)
                builder.set_negative_button("Анонимно", do_anon)
                builder.set_neutral_button("Отмена", lambda bld, w: bld.dismiss() if bld else None)
                try:
                    builder.make_button_red(AlertDialogBuilder.BUTTON_POSITIVE)
                except Exception:
                    pass
            else:
                builder.set_title("Открыть ссылку?")
                builder.set_message(f"{host}\n\n{url}")
                builder.set_positive_button("Открыть", do_open)
                builder.set_negative_button("Анонимно", do_anon)
                builder.set_neutral_button("Отмена", lambda bld, w: bld.dismiss() if bld else None)
            builder.create()
            builder.set_cancelable(True)
            builder.set_on_dismiss_listener(lambda bld: self._clear_active_link(url))
            builder.show()
            with self._verdict_lock:
                self._active_link = (url, builder)
        except Exception as e:
            log(f"Pocket Guard link dialog error: {e}")
            if dangerous:
                BulletinHelper.show_error("Pocket Guard: опасная ссылка, открытие отменено", frag)
                return
            # Диалог построить не удалось — открываем как обычно, чтобы не терять ссылку.
            self._reopen(context, url)

    def _clear_active_link(self, url: str):
        with self._verdict_lock:
            if self._active_link is not None and self._active_link[0] == url:
                self._active_link = None

    def _reopen(self, context, url: str):
        if context is None:
            frag = get_last_fragment()
            context = frag.getParentActivity() if frag else None
        if context is None or Browser is None:
            BulletinHelper.show_error("Pocket Guard: не удалось открыть ссылку", get_last_fragment())
            return
        self._bypass = True
        try:
            Browser.openUrl(context, url)
        except Exception as e:
            log(f"Pocket Guard open failed: {e}")
        finally:
            self._bypass = False

    # ------------------------------------------------------------------
    # Пауза подтверждений
    # ------------------------------------------------------------------

    def _on_snooze_click(self, context: Dict[str, Any]):
        self._snooze_until = time.time() + 3600.0
        BulletinHelper.show_info("Pocket Guard: подтверждения отключены на 1 час", get_last_fragment())

    # ------------------------------------------------------------------
    # Общий помощник диалогов (для справки)
    # ------------------------------------------------------------------

    def _show_dialog(self, title: str, message: str):
        frag = get_last_fragment()
        activity = frag.getParentActivity() if frag else None
        if not activity:
            BulletinHelper.show_info(title, frag)
            return
        builder = AlertDialogBuilder(activity)
        builder.set_title(title)
        builder.set_message(message)
        builder.set_positive_button("Понятно", lambda bld, w: bld.dismiss() if bld else None)
        builder.create()
        builder.set_cancelable(True)
        builder.show()
