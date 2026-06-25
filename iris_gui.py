"""
IRIS — Tabbed parent GUI (M1) · PyQt6 liquid-glass version
==========================================================
Tab 1 — Chat with local Llama 3.2 3B (Ollama). Glass bubbles, avatar tiles,
        pill badges, snapshot cards, suggestion chips, session sidebar,
        glass input bar. Recording awareness is handled by iris_query.py;
        session history (sidebar) by iris_sessions.py.
Tab 2 — Audio (embedded glass Qt dashboard driving the Phase 9 backend).
Tab 3 — Location (Leaflet map)
Tab 4 — People (M5 placeholder)
Tab 5 — Stream (M2 placeholder)
Run (from inside the project folder):
    pip install PyQt6 ollama requests
    python iris_gui.py
"""
from __future__ import annotations
import os
import re
import sys
import json
import math
import wave
import queue
import glob
import random
import shutil
import socket
import time
import tempfile
import subprocess
import threading
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional
from PyQt6.QtCore import Qt, QTimer, pyqtSignal, QObject, QSize, QRectF, QPoint
from PyQt6.QtGui import (
    QColor, QLinearGradient, QPainter, QBrush, QFont, QFontDatabase,
    QPainterPath, QPen, QShortcut, QKeySequence, QGuiApplication, QPixmap,
)
from PyQt6.QtWidgets import (
    QApplication, QWidget, QLabel, QFrame, QLineEdit, QPushButton,
    QVBoxLayout, QHBoxLayout, QScrollArea, QGraphicsDropShadowEffect,
    QStackedWidget, QFileDialog, QSizePolicy, QSizeGrip,
    QGridLayout, QTextEdit, QComboBox, QDialog,
)
# Optional: real map needs PyQt6-WebEngine. Degrades to a glass list if absent.
try:
    from PyQt6.QtWebEngineWidgets import QWebEngineView
except Exception:
    QWebEngineView = None
# Optional: location sidecars (present in the Phase 9 backend).
try:
    from location_phase8 import load_location_sidecar   # type: ignore
except Exception:
    def load_location_sidecar(_path):                    # graceful fallback
        return None
# ── Recording-request engine + session history. Imported defensively so the
#    app still launches if a module is missing (chat just loses that feature).
try:
    import iris_query as iq                              # type: ignore
except Exception:
    iq = None
try:
    import iris_sessions as isess                        # type: ignore
except Exception:
    isess = None
try:
    import iris_photos as iphotos                        # type: ignore
except Exception:
    iphotos = None
# ── Backend imports are defensive so the chat tab runs even without the full
#    Phase 9 backend present (recordings still work via disk scan). ──────────
try:
    import config_phase9 as config            # type: ignore
except Exception:
    config = None
try:
    from main_phase9 import Controller        # type: ignore
except Exception:
    Controller = None
try:
    from ollama import Client as OllamaClient
except ImportError:
    OllamaClient = None
def _cfg(attr: str, default):
    """Read an attribute from config_phase9 with a fallback."""
    if config is not None:
        v = getattr(config, attr, None)
        if v is not None:
            return v
    return default
OLLAMA_URL   = _cfg("OLLAMA_URL", "http://localhost:11434")
OLLAMA_MODEL = _cfg("OLLAMA_MODEL", "llama3.2:3b")
# ── Photo capture — screenshot is the default and only active path. The
# ESP32 camera trigger below is wired in per the integration guide but OFF
# by default; flip ESP32_CAMERA_ENABLED in config_phase9.py once the camera
# board is actually available to test with. When on, it's still a fallback:
# if the camera doesn't respond in time, we still take a screenshot so the
# capture never just does nothing. No firmware changes are needed for this —
# the protocol below is exactly what terminal.py already implements. ────────
ESP32_CAMERA_ENABLED      = bool(_cfg("ESP32_CAMERA_ENABLED", False))
ESP32_CAMERA_IP           = _cfg("ESP32_CAMERA_IP", "192.168.1.210")
ESP32_CAMERA_PHOTO_PORT   = int(_cfg("ESP32_CAMERA_PHOTO_PORT", 5006))
# Where the EXISTING receiver app (terminal.py, run by Ali/Humza) already
# saves incoming photos. We watch this folder instead of opening our own
# listener on 5011 — that port is already owned by their receiver on the PC.
ESP32_CAMERA_PHOTOS_DIR   = _cfg(
    "ESP32_CAMERA_PHOTOS_DIR",
    os.path.join(os.path.expanduser("~"), "Desktop", "camera_photos"))
ESP32_CAMERA_WAIT_SECONDS = float(_cfg("ESP32_CAMERA_WAIT_SECONDS", 20.0))
# ─────────────────────────────────────────────────────────────────────────────
# Palette
# ─────────────────────────────────────────────────────────────────────────────
BG_TOP        = "#0b1120"
BG_MID        = "#121a2e"
BG_BOT        = "#1c1838"
TEXT_PRIMARY  = "#e6edf3"
TEXT_MUTED    = "#9ca3af"
TEXT_DIM      = "#6b7280"
TEXT_FAINT    = "#4b5563"
ACCENT        = "#5eead4"
ACCENT_HOVER  = "#2dd4bf"
USER_ACCENT   = "#a78bfa"
BADGE_FACE_FG  = "#34d399"
BADGE_VOICE_FG = "#60a5fa"
BADGE_LOC_FG   = "#fbbf24"
REC_FG         = "#34d399"
COLOR_STATUS_ON  = "#10b981"
COLOR_STATUS_OFF = "#6b7280"
COLOR_DANGER     = "#ef4444"
COLOR_RECORDING  = "#dc2626"
GLASS_FILL_TOP = "rgba(255,255,255,0.13)"
GLASS_FILL_MID = "rgba(255,255,255,0.055)"
GLASS_FILL_BOT = "rgba(255,255,255,0.03)"
GLASS_BORDER   = "rgba(255,255,255,0.14)"
GLASS_BORDER_SOFT = "rgba(255,255,255,0.08)"
BUBBLE_BORDER  = "rgba(255,255,255,0.24)"
WINDOW_RADIUS  = 22
WINDOW_OUTLINE = QColor(255, 255, 255, 42)
FONT_MONO = "Cascadia Code"
FONT_SANS = "Segoe UI"
def _glass_gradient_qss(radius: int = 16,
                        top: str = GLASS_FILL_TOP,
                        mid: str = GLASS_FILL_MID,
                        bot: str = GLASS_FILL_BOT,
                        border: str = GLASS_BORDER) -> str:
    return (
        f"background: qlineargradient(x1:0, y1:0, x2:0, y2:1, "
        f"stop:0 {top}, stop:0.45 {mid}, stop:1 {bot});"
        f"border: 1px solid {border};"
        f"border-radius: {radius}px;"
    )
def _add_glass_shadow(w: QWidget, blur: int = 26, dy: int = 6,
                      alpha: int = 150) -> None:
    eff = QGraphicsDropShadowEffect(w)
    eff.setBlurRadius(blur)
    eff.setXOffset(0)
    eff.setYOffset(dy)
    eff.setColor(QColor(0, 0, 0, alpha))
    w.setGraphicsEffect(eff)
# ─────────────────────────────────────────────────────────────────────────────
# Recording store — discovers recordings + transcripts/summaries from disk.
# Now also captures per-segment timestamps so the chat can answer "what was
# said at 5:30" and "when did we discuss X".
# ─────────────────────────────────────────────────────────────────────────────
RECORDINGS_DIR_OVERRIDE: Optional[str] = None
_AUDIO_EXTS = {".wav", ".mp3", ".m4a", ".flac", ".ogg", ".aac", ".wma",
               ".webm", ".mp4"}
@dataclass
class Recording:
    name: str
    path: str
    mtime: float
    duration_sec: Optional[float] = None
    transcript: str = ""
    summary: str = ""
    segments: list = field(default_factory=list)   # [{start,end,speaker,text}]
    @property
    def has_transcript(self) -> bool:
        return bool(self.transcript.strip())
    def when(self) -> str:
        try:
            return datetime.fromtimestamp(self.mtime).strftime("%b %d %H:%M")
        except Exception:
            return "—"
    def length(self) -> str:
        if not self.duration_sec:
            return "--:--"
        m, s = divmod(int(self.duration_sec), 60)
        return f"{m:02d}:{s:02d}"
    def label(self) -> str:
        return f"{self.name} · {self.length()} · {self.when()}"
class RecordingStore:
    """Discovers recordings + their transcripts/summaries. Never raises."""
    def __init__(self, controller=None, audio_gui=None):
        self.controller = controller
        self.audio_gui = audio_gui
        self._cache = None
        self._cache_t = 0.0
    def list_recent(self, limit: int = 8) -> list[Recording]:
        import time as _t
        now = _t.time()
        if self._cache is not None and (now - self._cache_t) < 2.0:
            recs = self._cache
        else:
            recs = self._live_recordings()
            if not recs:
                recs = self._scan_disk()
            recs.sort(key=lambda r: r.mtime, reverse=True)
            self._cache = recs
            self._cache_t = now
        return recs[:limit]
    def build(self, audio_path: str) -> Optional[Recording]:
        return self._build_recording(audio_path)
    def _live_recordings(self) -> list[Recording]:
        return []
    def _scan_disk(self) -> list[Recording]:
        out: list[Recording] = []
        seen: set[str] = set()
        visited = 0
        for base in self._candidate_dirs():
            try:
                for root, dirs, files in os.walk(base):
                    dirs[:] = [d for d in dirs if d.lower() not in
                               {"transcripts", "summaries", "photos",
                                "__pycache__", ".git", "node_modules",
                                "chroma", "sqlite"}]
                    for fn in files:
                        if Path(fn).suffix.lower() not in _AUDIO_EXTS:
                            continue
                        full = os.path.abspath(os.path.join(root, fn))
                        key = os.path.normcase(os.path.realpath(full))
                        if key in seen:
                            continue
                        seen.add(key)
                        rec = self._build_recording(full)
                        if rec:
                            out.append(rec)
                        visited += 1
                        if visited > 4000:
                            return out
            except Exception:
                continue
        return out
    def _candidate_dirs(self) -> list[str]:
        raw: list[str] = []
        if RECORDINGS_DIR_OVERRIDE:
            raw.append(RECORDINGS_DIR_OVERRIDE)
        for attr in ("RECORDINGS_DIR", "RECORDING_DIR", "AUDIO_DIR",
                     "AUDIO_OUT_DIR", "AUDIO_SAVE_DIR", "DATA_DIR",
                     "OUTPUT_DIR", "SAVE_DIR", "CLIPS_DIR"):
            v = getattr(config, attr, None) if config is not None else None
            if isinstance(v, (str, os.PathLike)) and str(v).strip():
                raw.append(str(v))
        roots = [os.getcwd()]
        try:
            roots.append(os.path.dirname(os.path.abspath(__file__)))
        except Exception:
            pass
        for r in roots:
            for sub in ("", "recordings", "Recordings", "audio", "Audio",
                        "data/recordings", "data/audio", "data", "clips",
                        "output", "outputs"):
                raw.append(os.path.join(r, sub))
        out, seen = [], set()
        for d in raw:
            try:
                rp = os.path.realpath(os.path.abspath(d))
            except Exception:
                continue
            key = os.path.normcase(rp)
            if key in seen:
                continue
            seen.add(key)
            if os.path.isdir(rp):
                out.append(rp)
        return out
    def _build_recording(self, audio_path: str) -> Optional[Recording]:
        try:
            stat = os.stat(audio_path)
        except Exception:
            return None
        name = os.path.basename(audio_path)
        transcript, summary, dur, segments = self._find_sidecars(audio_path)
        if dur is None:
            dur = self._wav_duration(audio_path)
        return Recording(
            name=name, path=audio_path, mtime=stat.st_mtime,
            duration_sec=dur, transcript=transcript, summary=summary,
            segments=segments,
        )
    def _find_sidecars(self, audio_path: str):
        p = Path(audio_path)
        stem = p.with_suffix("")
        d = p.parent
        transcript, summary, dur, segments = "", "", None, []
        for jpath in [str(stem) + ".json", str(stem) + ".transcript.json",
                      str(d / "transcripts" / (p.stem + ".json"))]:
            if os.path.isfile(jpath):
                t, s, du, segs = self._read_json(jpath)
                transcript = transcript or t
                summary = summary or s
                dur = dur if dur is not None else du
                segments = segments or segs
                break
        if not transcript:
            for tpath in [str(stem) + ".transcript.txt", str(stem) + ".txt",
                          str(stem) + ".transcript", str(stem) + ".srt",
                          str(stem) + ".vtt",
                          str(d / "transcripts" / (p.stem + ".txt")),
                          str(d / "transcripts" / (p.stem + ".srt"))]:
                if os.path.isfile(tpath):
                    transcript = self._clean_transcript(self._read_text(tpath))
                    break
        if not summary:
            for spath in [str(stem) + ".summary.txt", str(stem) + "_summary.txt",
                          str(stem) + ".summary",
                          str(d / "summaries" / (p.stem + ".txt")),
                          str(d / "summaries" / (p.stem + ".summary.txt"))]:
                if os.path.isfile(spath):
                    summary = self._read_text(spath).strip()
                    break
        return transcript, summary, dur, segments
    @staticmethod
    def _read_text(path: str) -> str:
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                return f.read()
        except Exception:
            return ""
    def _read_json(self, path: str):
        try:
            data = json.loads(self._read_text(path))
        except Exception:
            return "", "", None, []
        transcript, summary, dur, segments = "", "", None, []
        if isinstance(data, dict):
            summary = str(data.get("summary") or "").strip()
            dur = (data.get("duration_sec") or data.get("duration")
                   or data.get("duration_seconds"))
            try:
                dur = float(dur) if dur is not None else None
            except Exception:
                dur = None
            t = data.get("transcript")
            segs = data.get("segments") or data.get("words")
            if isinstance(segs, list):
                for seg in segs:
                    if isinstance(seg, dict):
                        txt = (seg.get("text") or seg.get("word") or "").strip()
                        if txt:
                            segments.append({
                                "start": seg.get("start"),
                                "end": seg.get("end"),
                                "speaker": seg.get("speaker"),
                                "text": txt,
                            })
            if isinstance(t, str) and t.strip():
                transcript = t
            elif segments:
                parts = []
                for seg in segments:
                    spk = seg.get("speaker")
                    txt = seg.get("text", "")
                    parts.append(f"{spk}: {txt}" if spk else txt)
                transcript = "\n".join(parts)
        return self._clean_transcript(transcript), summary, dur, segments
    @staticmethod
    def _clean_transcript(text: str) -> str:
        if not text:
            return ""
        lines = []
        for ln in text.splitlines():
            s = ln.strip()
            if not s:
                continue
            if s.isdigit():
                continue
            if "-->" in s or "→" in s and "]" not in s:
                continue
            s = re.sub(r"^\[[0-9:.\s→\->]+\]\s*", "", s)
            if s:
                lines.append(s)
        return "\n".join(lines).strip()
    @staticmethod
    def _wav_duration(path: str) -> Optional[float]:
        if Path(path).suffix.lower() != ".wav":
            return None
        try:
            with wave.open(path, "rb") as w:
                frames = w.getnframes()
                rate = w.getframerate()
                if rate:
                    return frames / float(rate)
        except Exception:
            return None
        return None
# ─────────────────────────────────────────────────────────────────────────────
# Photo capture — screenshot (always available) + an ESP32 camera trigger that
# is wired in but inactive unless ESP32_CAMERA_ENABLED is set. Kept as plain
# functions (not a class) since each one is a single, independent operation
# the chat tab calls directly.
# ─────────────────────────────────────────────────────────────────────────────
def _trigger_esp32_photo(ip: str, port: int, timeout: float = 5.0):
    """Send the documented 'take_photo\\n' trigger to the camera ESP32.
    Exactly the protocol terminal.py already uses — connect, send, close, no
    response expected. Returns (ok, error_message)."""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.settimeout(timeout)
        s.connect((ip, port))
        s.sendall(b"take_photo\n")
        s.close()
        return True, ""
    except Exception as exc:
        return False, str(exc)
def _grab_screenshot_to(path: str) -> bool:
    """Grab the primary screen and save it as a PNG. Must be called on the
    GUI thread — Qt screen capture isn't safe from a background thread."""
    try:
        screen = QGuiApplication.primaryScreen()
        if screen is None:
            return False
        pixmap = screen.grabWindow(0)
        if pixmap.isNull():
            return False
        return bool(pixmap.save(path, "PNG"))
    except Exception:
        return False
def _grab_webcam_to(path: str, camera_index: int = 0):
    """Capture one frame from a webcam and save it as a PNG. This is the
    default for a bare 'take a photo' / 'take a picture' — an actual photo
    of the person, not the screen. Uses OpenCV (cv2), which is already in
    the project's pip list. Does blocking device I/O (opening a camera can
    take a noticeable moment), so call this off the GUI thread. Returns
    (ok, error_message).
    Tries a few backend/index combinations before giving up: plain
    cv2.VideoCapture(index) often fails even with a perfectly good, free
    camera because OpenCV doesn't always pick the right backend on its own.
    DSHOW/MSMF are the ones that reliably work on Windows; AVFoundation is
    the one for macOS. Laptops with both a Windows Hello IR camera and a
    regular webcam also sometimes expose the IR one at index 0, so a couple
    of indices are tried too when the caller didn't ask for a specific one.
    If nothing opens at all, the final error message is platform-specific —
    Windows and macOS block camera access for different reasons and fix it
    in different places, so a single generic message wouldn't actually help
    on either one.
    """
    try:
        import cv2
    except ImportError:
        return False, "opencv-python isn't installed (pip install opencv-python)"
    if sys.platform.startswith("win"):
        backend_attempts = [cv2.CAP_DSHOW, cv2.CAP_MSMF, cv2.CAP_ANY]
    elif sys.platform == "darwin":
        backend_attempts = [cv2.CAP_AVFOUNDATION, cv2.CAP_ANY]
    else:
        backend_attempts = [cv2.CAP_V4L2, cv2.CAP_ANY]
    indices = [camera_index] if camera_index else [0, 1, 2]
    last_err = "no webcam found"
    for idx in indices:
        for backend in backend_attempts:
            cap = None
            try:
                cap = cv2.VideoCapture(idx, backend)
                if not cap.isOpened():
                    last_err = "no webcam found"
                    continue
                # Many webcams' first frames are dark/off-color before
                # auto-exposure/auto-white-balance settle — warm up first.
                for _ in range(8):
                    cap.read()
                ok, frame = cap.read()
                if not ok or frame is None:
                    last_err = "the webcam opened but didn't return a frame"
                    continue
                if not cv2.imwrite(path, frame):
                    last_err = "couldn't save the captured frame"
                    continue
                return True, ""
            except Exception as e:
                last_err = str(e)
            finally:
                if cap is not None:
                    cap.release()
    if last_err == "no webcam found":
        if sys.platform.startswith("win"):
            last_err = (
                "no webcam found \u2014 if you do have one, this is almost "
                "always Windows blocking it silently: open Settings \u2192 "
                "Privacy & security \u2192 Camera, and make sure both "
                "'Camera access' and 'Let desktop apps access your camera' "
                "are ON. Desktop apps like this one don't get a permission "
                "popup the way browser/Store apps do \u2014 if that toggle "
                "is off, access is just denied with no prompt at all.")
        elif sys.platform == "darwin":
            last_err = (
                "no webcam found \u2014 if you do have one, macOS has "
                "probably blocked it. The first time an app uses the "
                "camera, macOS asks for permission \u2014 but if that was "
                "denied (or missed) before, it won't ask again. Open System "
                "Settings \u2192 Privacy & Security \u2192 Camera, and make "
                "sure it's turned on for whatever's actually running this "
                "script \u2014 Terminal, iTerm, VS Code, PyCharm, etc. \u2014 "
                "not 'Python', since that's what macOS attributes the "
                "request to. After enabling it you may need to fully quit "
                "and reopen that app.")
        else:
            last_err = (
                "no webcam found \u2014 check that a camera is actually "
                "connected, that no other app (browser tab, video call, "
                "etc.) already has it open, and that your user has "
                "permission to access /dev/video* (on some distros that "
                "means being in the 'video' group).")
    return False, last_err
def _photo_source_label(source: str, verbose: bool = False) -> str:
    """Human-readable label for a photo's capture source. verbose=True gives
    the longer 'captured ...' phrasing used in full chat sentences; the
    short form is used in compact captions and list lines."""
    if verbose:
        return {"esp32": "via the ESP32 camera",
                "webcam": "with the webcam"}.get(source, "as a screenshot")
    return {"esp32": "esp32", "webcam": "webcam"}.get(source, "screenshot")
def _photos_dir() -> str:
    """<recordings root>/photos — mirrors how transcripts/summaries already
    sit next to recordings. Always ensured to exist."""
    override = _cfg("PHOTOS_DIR", None)
    if override:
        base = str(override)
    else:
        base = None
        for d in RecordingStore()._candidate_dirs():
            base = d
            break
        if base is None:
            base = os.getcwd()
        base = os.path.join(base, "photos")
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return base
# ─────────────────────────────────────────────────────────────────────────────
# Glass widget primitives
# ─────────────────────────────────────────────────────────────────────────────
class GlassFrame(QFrame):
    def __init__(self, parent=None, radius: int = 16,
                 top=GLASS_FILL_TOP, mid=GLASS_FILL_MID, bot=GLASS_FILL_BOT,
                 border=GLASS_BORDER, shadow: bool = True,
                 blur: int = 26, dy: int = 6, shadow_alpha: int = 150):
        super().__init__(parent)
        self.setObjectName("glass")
        self.setStyleSheet(
            "QFrame#glass {" + _glass_gradient_qss(radius, top, mid, bot, border)
            + "}"
        )
        if shadow:
            _add_glass_shadow(self, blur=blur, dy=dy, alpha=shadow_alpha)
class Avatar(GlassFrame):
    def __init__(self, parent, initials: str, fg: str, tint: str):
        super().__init__(parent, radius=9,
                         top=f"rgba({_rgb(fg)},0.22)",
                         mid=f"rgba({_rgb(fg)},0.10)",
                         bot=f"rgba({_rgb(fg)},0.05)",
                         border=f"rgba({_rgb(fg)},0.35)",
                         blur=16, dy=3, shadow_alpha=120)
        self.setFixedSize(36, 36)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lbl = QLabel(initials)
        lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lbl.setStyleSheet(
            f"color:{fg}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:11px; font-weight:700;"
        )
        lay.addWidget(lbl)
class Pill(QLabel):
    def __init__(self, parent, text: str, fg: str):
        super().__init__(text, parent)
        self.setStyleSheet(
            f"color:{fg};"
            f"background: rgba({_rgb(fg)},0.12);"
            f"border: 1px solid rgba({_rgb(fg)},0.30);"
            f"border-radius: 8px; padding: 2px 9px;"
            f"font-family:'{FONT_MONO}','Consolas',monospace; font-size:10px;"
        )
        self.setSizePolicy(QSizePolicy.Policy.Maximum, QSizePolicy.Policy.Fixed)
class SnapshotCard(GlassFrame):
    def __init__(self, parent, label: str):
        super().__init__(parent, radius=10, blur=18, dy=4, shadow_alpha=120)
        self.setFixedSize(96, 76)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 8, 0, 6)
        lay.setSpacing(2)
        cam = QLabel("\U0001F4F7")
        cam.setAlignment(Qt.AlignmentFlag.AlignCenter)
        cam.setStyleSheet(f"color:{TEXT_DIM}; background:transparent;"
                          "border:none; font-size:22px;")
        cap = QLabel(label)
        cap.setAlignment(Qt.AlignmentFlag.AlignCenter)
        cap.setStyleSheet(f"color:{TEXT_MUTED}; background:transparent;"
                          f"border:none; font-family:'{FONT_MONO}','Consolas',"
                          "monospace; font-size:9px;")
        lay.addStretch(1)
        lay.addWidget(cam)
        lay.addWidget(cap)
        lay.addStretch(1)
class PhotoThumb(GlassFrame):
    """An actual image preview card — used for captured photos (chat inline
    confirmation + the Photos tab gallery). Separate from SnapshotCard, which
    stays a placeholder-style icon card used elsewhere. Optionally clickable
    (used by the Photos tab to make a photo the active chat reference) —
    existing call sites that don't pass on_click are unaffected.
    Fixed width AND height so QGridLayout can never stretch it to fill a row
    (that was the cause of the tall vertical-bar bug — a grid cell with only
    one row of content stretches to fill the whole scroll area unless the
    widget inside refuses to grow)."""
    def __init__(self, parent, image_path: str, caption: str,
                 size: int = 140, on_click=None):
        super().__init__(parent, radius=10, blur=18, dy=4, shadow_alpha=120)
        self._on_click = on_click
        if on_click is not None:
            self.setCursor(Qt.CursorShape.PointingHandCursor)
        cap_h = 34                          # room for two short caption lines
        self.setFixedSize(size, size + cap_h)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(6, 6, 6, 6)
        lay.setSpacing(4)
        pic = QLabel()
        pic.setAlignment(Qt.AlignmentFlag.AlignCenter)
        pic.setFixedSize(size - 12, size - 12)
        pic.setStyleSheet("background: rgba(0,0,0,0.25); border-radius:8px;"
                          "border:none;")
        pm = QPixmap()
        pm.load(image_path)
        if pm.isNull():
            pm.load(image_path, "JPEG")
        if not pm.isNull():
            pic.setPixmap(pm.scaled(
                size - 12, size - 12,
                Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                Qt.TransformationMode.SmoothTransformation))
        else:
            pic.setText("\U0001F4F7")
            pic.setStyleSheet(pic.styleSheet() + f"color:{TEXT_DIM}; font-size:24px;")
        lay.addWidget(pic)
        cap_lbl = QLabel(caption)
        cap_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        cap_lbl.setWordWrap(True)
        cap_lbl.setFixedHeight(cap_h - 4)
        cap_lbl.setStyleSheet(f"color:{TEXT_PRIMARY}; background:transparent;"
                              f"border:none; font-family:'{FONT_MONO}',"
                              "'Consolas',monospace; font-size:11px;")
        lay.addWidget(cap_lbl)
    def mousePressEvent(self, event) -> None:
        if self._on_click is not None and \
                event.button() == Qt.MouseButton.LeftButton:
            self._on_click()
        super().mousePressEvent(event)
class SuggestionChip(QPushButton):
    def __init__(self, parent, text: str, on_click):
        super().__init__(text, parent)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setStyleSheet(
            "QPushButton {"
            f"color:{TEXT_MUTED};"
            f"background: rgba(255,255,255,0.06);"
            f"border: 1px solid {GLASS_BORDER_SOFT};"
            "border-radius: 15px; padding: 6px 14px;"
            f"font-family:'{FONT_SANS}'; font-size:11px;"
            "}"
            "QPushButton:hover { background: rgba(255,255,255,0.11); }"
        )
        self.clicked.connect(lambda: on_click(text))
        _add_glass_shadow(self, blur=14, dy=3, alpha=110)
def _rgb(hex_color: str) -> str:
    h = hex_color.lstrip("#")
    return f"{int(h[0:2],16)},{int(h[2:4],16)},{int(h[4:6],16)}"
class BubbleLabel(QLabel):
    MAXW = 500
    def __init__(self, text: str = ""):
        super().__init__("")
        f = QFont(FONT_MONO)
        f.setPixelSize(13)
        self.setFont(f)
        self.setWordWrap(True)
        self.setTextInteractionFlags(
            Qt.TextInteractionFlag.TextSelectableByMouse)
        self.setText(text)
    def setText(self, text: str) -> None:
        super().setText(text)
        fm = self.fontMetrics()
        widest = max((fm.horizontalAdvance(ln)
                      for ln in str(text).split("\n")), default=0)
        self.setFixedWidth(min(widest + 2, self.MAXW))
        self.updateGeometry()
class GradientBackground(QWidget):
    def paintEvent(self, _evt):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        g = QLinearGradient(0, 0, self.width(), self.height())
        g.setColorAt(0.0, QColor(BG_TOP))
        g.setColorAt(0.55, QColor(BG_MID))
        g.setColorAt(1.0, QColor(BG_BOT))
        p.fillRect(self.rect(), QBrush(g))
# ─────────────────────────────────────────────────────────────────────────────
# Tab 1 — Chat (glass). Recording understanding via iris_query; session history
# via iris_sessions. Rendering + threading are Qt.
# ─────────────────────────────────────────────────────────────────────────────
class ChatTab(QWidget):
    _main_invoke = pyqtSignal(object)
    def __init__(self, parent=None, controller=None, audio_gui=None,
                 switch_to_audio=None):
        super().__init__(parent)
        self._switch_to_audio = switch_to_audio
        self.history: list[dict] = []
        self.busy: bool = False
        self._client: Optional[object] = None
        self.store = RecordingStore(controller=controller, audio_gui=audio_gui)
        self._active: Optional[Recording] = None
        self._pending_pick: Optional[list[Recording]] = None
        self._polling: set[str] = set()
        self._system_prompt = (
            "You are IRIS, a local assistant. You can read the user's audio "
            "recordings, including their transcripts and summaries. When a "
            "recording's transcript is provided to you below, answer strictly "
            "from it and never invent details. If something isn't in the "
            "transcript, say so. Be concise, and when summarizing a recording, "
            "offer 2-3 specific follow-up questions the user could ask about it. "
            "If no transcript is included in the message you are answering, "
            "you do NOT have access to any recording's contents: do not guess "
            "or invent what a recording says, and say it isn't available."
        )
        # Session history (sidebar). Degrades gracefully if the module is gone.
        self._sessions = isess.SessionStore() if isess is not None else None
        self._session = (self._sessions.new_session()
                         if self._sessions is not None else None)
        # Photo capture store. Degrades gracefully if the module is gone.
        self._photos = (iphotos.PhotoStore(_photos_dir())
                        if iphotos is not None else None)
        # The currently-selected photo (clicked in the Photos tab, or
        # resolved by a chat query) — lets follow-ups reference "this photo".
        self._active_photo: Optional[object] = None
        self._main_invoke.connect(lambda fn: fn())
        self._build_ui()
        self._init_ollama()
    # -- run something on the GUI thread from any thread --
    def _call_main(self, fn) -> None:
        self._main_invoke.emit(fn)
    # ── session logging ──────────────────────────────────────────────────
    def _log(self, role: str, content: str) -> None:
        if self._sessions is not None and self._session is not None:
            try:
                self._sessions.add_message(self._session.id, role, content)
                self._refresh_sidebar()
            except Exception:
                pass
    # ── UI scaffold ──────────────────────────────────────────────────────
    def _build_ui(self) -> None:
        root = QHBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)
        root.addWidget(self._build_sidebar())
        root.addWidget(self._build_main_pane(), 1)
    # ── Sidebar (live session history) ───────────────────────────────────
    def _build_sidebar(self) -> QWidget:
        panel = GlassFrame(self, radius=16, shadow=True, blur=24, dy=6,
                           shadow_alpha=120,
                           top="rgba(255,255,255,0.06)",
                           mid="rgba(255,255,255,0.035)",
                           bot="rgba(255,255,255,0.02)",
                           border=GLASS_BORDER_SOFT)
        panel.setFixedWidth(236)
        lay = QVBoxLayout(panel)
        lay.setContentsMargins(14, 16, 14, 16)
        lay.setSpacing(0)
        new_btn = QPushButton("+  new session")
        new_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        new_btn.setFixedHeight(34)
        new_btn.setStyleSheet(
            "QPushButton {"
            f"color:{ACCENT}; background: rgba({_rgb(ACCENT)},0.12);"
            f"border:1px solid rgba({_rgb(ACCENT)},0.30); border-radius:11px;"
            f"font-family:'{FONT_SANS}'; font-size:12px; font-weight:700; }}"
            f"QPushButton:hover {{ background: rgba({_rgb(ACCENT)},0.20); }}")
        new_btn.clicked.connect(self._new_session)
        lay.addWidget(new_btn)
        lay.addSpacing(10)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(
            Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setStyleSheet(
            "QScrollArea{background:transparent;border:none;}"
            "QScrollBar:vertical{width:6px;background:transparent;}"
            "QScrollBar::handle:vertical{background:rgba(255,255,255,0.14);"
            "border-radius:3px;}")
        self._sidebar_holder = QWidget()
        self._sidebar_holder.setStyleSheet("background: transparent;")
        self._sidebar_lay = QVBoxLayout(self._sidebar_holder)
        self._sidebar_lay.setContentsMargins(0, 0, 4, 0)
        self._sidebar_lay.setSpacing(0)
        self._sidebar_lay.addStretch(1)
        scroll.setWidget(self._sidebar_holder)
        lay.addWidget(scroll, 1)
        self._refresh_sidebar()
        return panel
    def _refresh_sidebar(self) -> None:
        lay = getattr(self, "_sidebar_lay", None)
        if lay is None:
            return
        while lay.count() > 1:                       # keep the trailing stretch
            item = lay.takeAt(0)
            w = item.widget()
            if w:
                w.deleteLater()
        groups = (self._sessions.grouped(exclude=None)
                  if self._sessions is not None else [])
        active_id = self._session.id if self._session is not None else None
        if not groups:
            lay.insertWidget(0, self._section("TODAY"))
            lay.insertWidget(1, self._session_label("new session", active=True))
            return
        idx = 0
        for label, sessions in groups:
            lay.insertWidget(idx, self._section(label)); idx += 1
            for s in sessions:
                row = self._session_label(s.title, active=(s.id == active_id),
                                          sid=s.id)
                lay.insertWidget(idx, row); idx += 1
    def _section(self, text: str) -> QLabel:
        lbl = QLabel(text.upper())
        lbl.setStyleSheet(
            f"color:{TEXT_DIM}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:9px; font-weight:700;"
            "padding: 14px 4px 4px 4px; letter-spacing:1px;")
        return lbl
    def _session_label(self, text: str, active: bool = False,
                       sid: Optional[str] = None) -> QWidget:
        dot = "\u25CF" if active else "\u25CB"
        color = ACCENT if active else TEXT_MUTED
        weight = "700" if active else "400"
        btn = QPushButton(f"{dot}  {text}")
        btn.setCursor(Qt.CursorShape.PointingHandCursor)
        btn.setStyleSheet(
            "QPushButton {"
            f"color:{color}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:12px; font-weight:{weight};"
            "text-align:left; padding: 4px 4px; }"
            "QPushButton:hover { background: rgba(255,255,255,0.06);"
            "border-radius:8px; }")
        if sid is not None:
            btn.clicked.connect(lambda _=False, i=sid: self._load_session(i))
        return btn
    def _new_session(self) -> None:
        if self._sessions is not None:
            self._session = self._sessions.new_session()
        self.history.clear()
        self._active = None
        self._active_photo = None
        self._pending_pick = None
        self._clear_log()
        self._init_ollama()
        self._refresh_sidebar()
    def _load_session(self, sid: str) -> None:
        if self._sessions is None:
            return
        s = self._sessions.get(sid)
        if s is None:
            return
        self._session = s
        self.history = [{"role": m["role"], "content": m["content"]}
                        for m in s.messages]
        self._active = None
        self._active_photo = None
        self._pending_pick = None
        self._clear_log()
        for m in s.messages:
            if m["role"] == "user":
                self._append_user(m["content"], log=False)
            else:
                self._append_iris(m["content"], log=False)
        self._refresh_sidebar()
    def _clear_log(self) -> None:
        lay = self.chat_log
        while lay.count() > 1:
            item = lay.takeAt(0)
            w = item.widget()
            if w:
                w.deleteLater()
    # ── Main pane ────────────────────────────────────────────────────────
    def _build_main_pane(self) -> QWidget:
        pane = QWidget(self)
        lay = QVBoxLayout(pane)
        lay.setContentsMargins(22, 18, 22, 18)
        lay.setSpacing(0)
        header = QHBoxLayout()
        title = QLabel("new session")
        title.setStyleSheet(
            f"color:{TEXT_PRIMARY}; background:transparent;"
            f"font-family:'{FONT_SANS}'; font-size:16px; font-weight:700;")
        header.addWidget(title)
        header.addStretch(1)
        rec_pill = Pill(pane, "\u25CF  ready", REC_FG)
        face_pill = Pill(pane, "face: \u2014", TEXT_DIM)
        header.addWidget(rec_pill)
        header.addSpacing(6)
        header.addWidget(face_pill)
        lay.addLayout(header)
        lay.addSpacing(8)
        self.scroll = QScrollArea(pane)
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.scroll.setHorizontalScrollBarPolicy(
            Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.scroll.setStyleSheet(
            "QScrollArea { background: transparent; border: none; }"
            "QScrollBar:vertical { background: transparent; width: 8px; }"
            "QScrollBar::handle:vertical {"
            "  background: rgba(255,255,255,0.14); border-radius: 4px; }"
            "QScrollBar::add-line, QScrollBar::sub-line { height: 0; }")
        self._log_holder = QWidget()
        self._log_holder.setStyleSheet("background: transparent;")
        self.chat_log = QVBoxLayout(self._log_holder)
        self.chat_log.setContentsMargins(2, 4, 12, 4)
        self.chat_log.setSpacing(0)
        self.chat_log.addStretch(1)
        self.scroll.setWidget(self._log_holder)
        lay.addWidget(self.scroll, 1)
        chips = QHBoxLayout()
        chips.setContentsMargins(0, 6, 0, 6)
        chips.addWidget(SuggestionChip(pane, "what's in my last recording?",
                                       self._on_chip))
        chips.addSpacing(8)
        chips.addWidget(SuggestionChip(pane, "summarize today", self._on_chip))
        chips.addStretch(1)
        lay.addLayout(chips)
        input_bar = GlassFrame(pane, radius=22, blur=22, dy=5, shadow_alpha=150)
        input_bar.setFixedHeight(54)
        ib = QHBoxLayout(input_bar)
        ib.setContentsMargins(18, 0, 8, 0)
        ib.setSpacing(8)
        prefix = QLabel(">")
        prefix.setStyleSheet(
            f"color:{TEXT_DIM}; background:transparent; border:none;"
            f"font-family:'{FONT_MONO}','Consolas',monospace;"
            "font-size:16px; font-weight:700;")
        ib.addWidget(prefix)
        self.input = QLineEdit()
        self.input.setPlaceholderText("ask iris anything\u2026")
        self.input.setStyleSheet(
            f"QLineEdit {{ color:{TEXT_PRIMARY}; background:transparent;"
            f"border:none; font-family:'{FONT_SANS}'; font-size:13px; }}")
        self.input.returnPressed.connect(self._on_submit)
        ib.addWidget(self.input, 1)
        self.status_dot = QLabel("\u25A0")
        self.status_dot.setStyleSheet(
            f"color:{ACCENT}; background:transparent; border:none; font-size:13px;")
        ib.addWidget(self.status_dot)
        mic = QPushButton("\U0001F399")
        mic.setCursor(Qt.CursorShape.PointingHandCursor)
        mic.setFixedSize(38, 38)
        mic.setStyleSheet(
            "QPushButton {"
            f"background: qlineargradient(x1:0,y1:0,x2:0,y2:1,"
            f"stop:0 rgba({_rgb(ACCENT)},0.95), stop:1 rgba({_rgb(ACCENT_HOVER)},0.95));"
            f"color:{BG_TOP}; border:none; border-radius:19px; font-size:16px; }}"
            f"QPushButton:hover {{ background: {ACCENT_HOVER}; }}")
        _add_glass_shadow(mic, blur=16, dy=3, alpha=130)
        ib.addWidget(mic)
        camera_btn = QPushButton("\U0001F4F7")
        camera_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        camera_btn.setFixedSize(38, 38)
        camera_btn.setToolTip("Take a photo now")
        camera_btn.setStyleSheet(
            "QPushButton {"
            f"background: rgba(255,255,255,0.08);"
            f"border: 1px solid {GLASS_BORDER_SOFT};"
            "border-radius:19px; font-size:15px; }"
            "QPushButton:hover { background: rgba(255,255,255,0.14); }")
        _add_glass_shadow(camera_btn, blur=14, dy=3, alpha=110)
        camera_btn.clicked.connect(self._on_manual_photo_button)
        ib.addWidget(camera_btn)
        lay.addSpacing(6)
        lay.addWidget(input_bar)
        return pane
    # ── Ollama ───────────────────────────────────────────────────────────
    def _init_ollama(self) -> None:
        if OllamaClient is None:
            self._append_iris("(ollama python package missing — pip install ollama)",
                              log=False)
            return
        try:
            self._client = OllamaClient(host=OLLAMA_URL)
            self._append_iris(
                f"Session started. Connected to {OLLAMA_MODEL}. "
                f"Ask me anything — including about your audio recordings, "
                f"e.g. \u201cwhat's my last recording?\u201d",
                pills=[("voice match", BADGE_VOICE_FG)], log=False)
        except Exception as exc:
            self._append_iris(f"(could not connect to Ollama: {exc})", log=False)
    # ── Message rendering ────────────────────────────────────────────────
    def _append_iris(self, body: str,
                     pills: list[tuple[str, str]] | None = None,
                     snapshots: list[str] | None = None,
                     photo_paths: list[str] | None = None,
                     log: bool = True) -> QLabel:
        if log:
            self._log("assistant", body)
        return self._render_message(
            "iris", body, is_user=False, avatar_initials="AI",
            avatar_fg=ACCENT, pills=pills, snapshots=snapshots,
            photo_paths=photo_paths)
    def _append_user(self, body: str, log: bool = True) -> QLabel:
        if log:
            self._log("user", body)
        return self._render_message(
            "you", body, is_user=True, avatar_initials="MA",
            avatar_fg=USER_ACCENT)
    def _render_message(self, author: str, body: str, is_user: bool,
                        avatar_initials: str, avatar_fg: str,
                        pills: list[tuple[str, str]] | None = None,
                        snapshots: list[str] | None = None,
                        photo_paths: list[str] | None = None) -> QLabel:
        row = QWidget()
        row.setStyleSheet("background: transparent;")
        rlay = QHBoxLayout(row)
        rlay.setContentsMargins(4, 10, 4, 0)
        rlay.setSpacing(12)
        avatar = Avatar(row, avatar_initials, avatar_fg, avatar_fg)
        col = QVBoxLayout()
        col.setContentsMargins(0, 0, 0, 0)
        col.setSpacing(4)
        rlay.addWidget(avatar, 0, Qt.AlignmentFlag.AlignTop)
        rlay.addLayout(col, 1)
        head = QHBoxLayout()
        head.setSpacing(8)
        name = QLabel(author)
        name.setStyleSheet(
            f"color:{avatar_fg}; background:transparent; border:none;"
            f"font-family:'{FONT_MONO}','Consolas',monospace;"
            "font-size:11px; font-weight:700;")
        head.addWidget(name)
        tm = QLabel(f"\u00b7  {datetime.now().strftime('%H:%M')}")
        tm.setStyleSheet(
            f"color:{TEXT_DIM}; background:transparent; border:none;"
            f"font-family:'{FONT_MONO}','Consolas',monospace; font-size:10px;")
        head.addWidget(tm)
        if pills:
            for text, fg in pills:
                head.addWidget(Pill(row, text, fg))
        head.addStretch(1)
        col.addLayout(head)
        bubble = GlassFrame(row, radius=14, border=BUBBLE_BORDER,
                            blur=22, dy=5, shadow_alpha=140)
        blay = QVBoxLayout(bubble)
        blay.setContentsMargins(16, 11, 16, 11)
        body_lbl = BubbleLabel(body)
        body_lbl.setStyleSheet(
            f"color:{TEXT_PRIMARY}; background:transparent; border:none;")
        blay.addWidget(body_lbl)
        brow = QHBoxLayout()
        brow.setContentsMargins(0, 0, 0, 0)
        brow.addWidget(bubble)
        brow.addStretch(1)
        col.addLayout(brow)
        if snapshots:
            snaps = QHBoxLayout()
            snaps.setContentsMargins(0, 6, 0, 2)
            snaps.setSpacing(8)
            for label in snapshots:
                snaps.addWidget(SnapshotCard(row, label))
            snaps.addStretch(1)
            col.addLayout(snaps)
        if photo_paths:
            pics = QHBoxLayout()
            pics.setContentsMargins(0, 6, 0, 2)
            pics.setSpacing(8)
            for p in photo_paths:
                cap = os.path.basename(p)
                pics.addWidget(PhotoThumb(row, p, cap))
            pics.addStretch(1)
            col.addLayout(pics)
        self.chat_log.insertWidget(self.chat_log.count() - 1, row)
        QTimer.singleShot(0, self._scroll_to_bottom)
        return body_lbl
    def _scroll_to_bottom(self) -> None:
        bar = self.scroll.verticalScrollBar()
        bar.setValue(bar.maximum())
    def _on_chip(self, text: str) -> None:
        self.input.setText(text)
        self.input.setFocus()
    # ══════════════════════════════════════════════════════════════════════
    # Routing — pending picks first, then the iris_query classifier.
    # ══════════════════════════════════════════════════════════════════════
    def _on_submit(self) -> None:
        if self.busy:
            return
        text = self.input.text().strip()
        if not text:
            return
        self.input.clear()
        self._append_user(text)
        self.history.append({"role": "user", "content": text})
        low = text.lower().strip()
        # (1) A reply that picks from the most recently shown list. The list is
        # kept after a pick so several recordings can be chosen from one list.
        if self._pending_pick and self._is_pick_reply(low):
            rec = self._resolve_pending(low, self._pending_pick)
            if rec is not None:
                self._start_bg(lambda: self._handle_recording(rec))
                return
            n = len(self._pending_pick)
            self._append_iris(
                f"I didn't catch which one. Reply with a number (1-{n}), "
                "a time like 09:40, or a duration like '6 seconds'.")
            return
        # (2) Classify the request with the language engine.
        if iq is None:
            self._start_bg(lambda: self._ask_ollama(text))
            return
        intent = iq.classify(text, self._all_recordings(),
                             datetime.now(), has_active=bool(self._active))
        self._dispatch_intent(intent, text)
    def _dispatch_intent(self, intent, text: str) -> None:
        k = intent.kind
        if k == "photo":
            self._trigger_photo_capture(intent.corrected_text or text,
                                        mode=intent.capture_mode)
            return
        if k == "photo_query":
            self._do_photo_query(intent)
            return
        if k == "list":
            if intent.summarize_all:
                recs = [r for r in self._all_recordings()
                        if iq.is_meaningful(r)]
                self._summarize_many(recs, "all recordings")
            else:
                self._append_iris(self._list_recordings_text())
            return
        if k == "latest":
            rec = iq.latest(self._all_recordings())
            if rec is None:
                self._append_iris("I don't see any recordings yet.")
            else:
                self._start_bg(lambda: self._handle_recording(rec))
            return
        if k == "random":
            pool = [r for r in self._all_recordings() if iq.is_meaningful(r)]
            if not pool:
                self._append_iris("I don't see any recordings to pick from.")
            else:
                rec = random.choice(pool)
                self._start_bg(lambda: self._handle_recording(rec))
            return
        if k == "name":
            m = intent.name_matches
            if len(m) == 1:
                self._start_bg(lambda: self._handle_recording(m[0]))
            else:
                self._pending_pick = m[:30]
                self._append_iris(self._format_generic_pick(
                    m[:30], f"I found {len(m)} recordings that could match. "
                    "Which one?"))
            return
        if k == "date":
            self._do_date(intent)
            return
        if k == "date_range":
            self._do_range(intent)
            return
        if k == "index_range":
            self._do_index_range(intent)
            return
        if k == "month":
            self._do_month(intent)
            return
        if k == "time":
            self._do_time(intent)
            return
        if k == "content_search":
            self._do_content(intent)
            return
        # k == "none"
        if self._active is not None or self._active_photo is not None:
            self._start_bg(lambda: self._answer_followup(text))
            return
        self._start_bg(lambda: self._ask_ollama(text))
    # ── Photo capture ──────────────────────────────────────────────────────
    def _on_manual_photo_button(self) -> None:
        """The 📷 button — same action as typing 'take a photo', without
        needing iris_query.py to be present. Takes an actual photo (webcam),
        same as the new default for typed/voice triggers."""
        self._append_user("\U0001F4F7 take a photo")
        self.history.append({"role": "user", "content": "take a photo"})
        self._trigger_photo_capture("manual capture", mode="camera")
    def handle_voice_trigger(self, phrase: str) -> None:
        """Entry point for a wake-word trigger heard via live audio
        (AudioTab's live transcription listener), as opposed to typed chat
        text or the manual button. Posts a bubble showing what was heard,
        then reuses the exact same capture path as every other trigger
        source — nothing about the capture itself differs by source."""
        heard = (phrase or "").strip()
        self._append_user(f"\U0001F3A4 (heard) {heard}")
        self.history.append({"role": "user", "content": heard})
        mode = iq.photo_capture_mode(heard) if iq is not None else "camera"
        self._trigger_photo_capture(heard or "voice trigger", mode=mode)
    def _trigger_photo_capture(self, trigger_text: str,
                               mode: str = "camera") -> None:
        if self._photos is None:
            self._append_iris(
                "Photo capture isn't available — iris_photos.py is missing.")
            return
        if mode == "screen":
            self._capture_screenshot_now(trigger_text)
            return
        # mode == "camera" (the default for a bare "take a photo"/"take a
        # picture"): prefer the real ESP32 camera if it's enabled (still off
        # by default — see ESP32_CAMERA_ENABLED), otherwise the laptop's
        # built-in webcam.
        if ESP32_CAMERA_ENABLED:
            self._start_bg(lambda: self._capture_via_esp32(trigger_text))
        else:
            self._capture_webcam_now(trigger_text)
    def _capture_webcam_now(self, trigger_text: str) -> None:
        """Webcam capture needs to open a device (can take a noticeable
        moment) so it runs on a background thread; only the final Qt
        posting happens back on the GUI thread via _call_main."""
        def work():
            path = self._photos.new_path("png")
            ok, err = _grab_webcam_to(path)
            self._call_main(lambda: self._finish_webcam_capture(
                trigger_text, path if ok else None, err))
        threading.Thread(target=work, daemon=True).start()
    def _finish_webcam_capture(self, trigger_text: str,
                               path: Optional[str], err: str) -> None:
        if not path:
            msg = f"I couldn't take a photo \u2014 {err}."
            self._append_iris(msg)
            self.history.append({"role": "assistant", "content": msg})
            return
        self._photos.record(path, source="webcam", trigger_text=trigger_text)
        msg = "\U0001F4F8 Got it \u2014 snapped a photo."
        self._append_iris(msg, photo_paths=[path])
        self.history.append({"role": "assistant", "content": msg})
    def _capture_screenshot_now(self, trigger_text: str,
                                note: str = "") -> None:
        """Grab + save a screenshot. Must run on the GUI thread."""
        path = self._photos.new_path("png")
        if not _grab_screenshot_to(path):
            fail_msg = "I couldn't capture a screenshot just now."
            self._append_iris(fail_msg)
            self.history.append({"role": "assistant", "content": fail_msg})
            return
        self._photos.record(path, source="screenshot",
                            trigger_text=trigger_text, note=note)
        msg = "\U0001F4F8 Got it — saved a screenshot."
        if note:
            msg += f" {note}"
        self._append_iris(msg, photo_paths=[path])
        self.history.append({"role": "assistant", "content": msg})
    def _capture_via_esp32(self, trigger_text: str) -> str:
        """Background-thread work: trigger the real camera, wait for the
        existing receiver app to drop the JPEG, fall back to a screenshot if
        it doesn't arrive in time. The photo is saved to the store either
        way; this returns the single status text for the chat bubble (no
        separate thumbnail bubble here, to avoid posting twice for one
        action — the result is always visible in the Photos tab)."""
        since = time.time()        # baseline BEFORE triggering, so even a
        ok, err = _trigger_esp32_photo(ESP32_CAMERA_IP, ESP32_CAMERA_PHOTO_PORT)
        found = None
        if ok:
            deadline = since + ESP32_CAMERA_WAIT_SECONDS
            while time.time() < deadline:
                found = self._photos.newest_new_file(
                    ESP32_CAMERA_PHOTOS_DIR, since)
                if found:
                    break
                time.sleep(1.0)
        if found:
            ext = os.path.splitext(found)[1].lstrip(".") or "jpg"
            dest = self._photos.new_path(ext)
            try:
                shutil.copy2(found, dest)
            except Exception:
                dest = found
            self._photos.record(dest, source="esp32", trigger_text=trigger_text)
            time.sleep(0.3)   # let the file fully flush before Qt loads the thumbnail
            msg = "\U0001F4F8 Got it \u2014 photo received from the ESP32 camera."
            self._call_main(lambda d=dest, m=msg: self._append_iris(
                m, photo_paths=[d]))
            return ""  # empty: _finish_response will remove the thinking bubble cleanly
        # Fallback: hop to the GUI thread for the screenshot grab and wait
        # for it to finish before returning (keeps _start_bg's contract of
        # "background work returns the final text" intact).
        done = threading.Event()
        captured = {}
        def grab():
            path = self._photos.new_path("png")
            captured["ok"] = _grab_screenshot_to(path)
            captured["path"] = path
            done.set()
        self._call_main(grab)
        done.wait(timeout=5.0)
        path = captured.get("path") if captured.get("ok") else None
        reason = ("the camera didn't respond in time" if ok
                  else f"couldn't reach the camera ({err})")
        if not path:
            return f"I couldn't reach the camera ({reason}), and the " \
                   "screenshot fallback failed too."
        self._photos.record(path, source="screenshot", trigger_text=trigger_text,
                            note=f"esp32 fallback: {reason}")
        return f"\U0001F4F8 Took a screenshot instead \u2014 {reason}. See it " \
               "in the Photos tab."
    # ── Photo selection + lookup ──────────────────────────────────────────
    def select_photo(self, photo) -> None:
        """Make `photo` the active reference for chat follow-ups. Called both
        when a photo resolves a chat query and when one is clicked in the
        Photos tab gallery."""
        self._active_photo = photo
        tag = _photo_source_label(photo.source, verbose=True)
        msg = f"\U0001F4F7 That photo was taken {photo.when()}, captured {tag}"
        if photo.trigger_text:
            msg += f" (triggered by \u201c{photo.trigger_text}\u201d)"
        msg += (".\n\nI can tell you when or how it was captured, or you can "
                "reference it by date/time \u2014 I can't describe what's "
                "actually in the image, since there's no vision model "
                "wired into chat yet.")
        self._append_iris(msg, photo_paths=[photo.path])
        self.history.append({"role": "assistant", "content": msg})
    def _do_photo_query(self, intent) -> None:
        if self._photos is None:
            self._append_iris("Photo storage isn't available right now.")
            return
        photos = self._photos.list_all()           # newest first
        if not photos:
            self._append_iris(
                "I don't see any photos yet. Say \u201chey iris, take a "
                "photo\u201d or use the \U0001F4F7 button.")
            return
        action = intent.photo_action
        if action == "latest":
            self.select_photo(photos[0])
            return
        if action == "range" and intent.date_range:
            start, end = intent.date_range
            matches = self._photos_in_range(photos, start, end)
            self._show_photo_set(
                matches, f"{self._date_label(start)} \u2192 "
                f"{self._date_label(end)}")
            return
        if action == "date" and intent.dates:
            d = intent.dates[0]
            matches = self._photos_on_date(photos, d)
            if intent.time is not None and matches:
                narrowed = [p for p in matches
                           if self._photo_time_matches(p, intent.time)]
                matches = narrowed or matches
            self._show_photo_set(matches, self._date_label(d))
            return
        if action == "time" and intent.time:
            matches = [p for p in photos
                      if self._photo_time_matches(p, intent.time)]
            h, mi, s = intent.time
            clock = f"{h:02d}:{mi:02d}" + (f":{s:02d}" if s is not None else "")
            self._show_photo_set(matches, clock)
            return
        # action == "all" (or anything unrecognized) -> the most recent batch
        self._show_photo_set(photos[:8],
                             "your photos" if len(photos) > 1 else "your photo")
    def _show_photo_set(self, photos, label: str) -> None:
        if not photos:
            self._append_iris(f"I don't see any photos for {label}.")
            return
        if len(photos) == 1:
            self.select_photo(photos[0])
            return
        shown = photos[:8]
        lines = [f"\U0001F4F8 {len(photos)} photo{'s' if len(photos) != 1 else ''} "
                f"for {label}:"]
        for p in shown:
            tag = _photo_source_label(p.source)
            lines.append(f"  \u2022 {p.when()} \u00b7 {tag}")
        if len(photos) > len(shown):
            lines.append(f"  \u2026and {len(photos) - len(shown)} more \u2014 "
                         "see the Photos tab.")
        text = "\n".join(lines)
        self._append_iris(text, photo_paths=[p.path for p in shown])
        self.history.append({"role": "assistant", "content": text})
    @staticmethod
    def _photos_on_date(photos, d) -> list:
        y, mo, day = d
        out = []
        for p in photos:
            dt = datetime.fromtimestamp(p.taken_at)
            if dt.month == mo and dt.day == day and (y is None or dt.year == y):
                out.append(p)
        return out
    @staticmethod
    def _photos_in_range(photos, start, end) -> list:
        def to_dt(dd):
            yy = (dd[0] if dd[0] is not None
                 else (start[0] or end[0] or datetime.now().year))
            return datetime(yy, dd[1], dd[2])
        lo, hi = to_dt(start), to_dt(end)
        if lo > hi:
            lo, hi = hi, lo
        hi = hi + timedelta(days=1)
        return [p for p in photos
                if lo <= datetime.fromtimestamp(p.taken_at) < hi]
    @staticmethod
    def _photo_time_matches(p, tm) -> bool:
        h, mi, s = tm
        dt = datetime.fromtimestamp(p.taken_at)
        if dt.hour != h or dt.minute != mi:
            return False
        if s is not None and dt.second != s:
            return False
        return True
    # ── date / range / month / time handlers ─────────────────────────────
    def _do_date(self, intent) -> None:
        recs = self._all_recordings()
        d = intent.dates[0]
        cands = iq.candidates_for_date(recs, d)
        if intent.time is not None:
            h, mi, s = intent.time
            nd = [r for r in cands if iq.rec_dt(r).hour == h
                  and iq.rec_dt(r).minute == mi
                  and (s is None or iq.rec_dt(r).second == s)]
            cands = nd or cands
        if not cands:
            self._append_iris(
                f"I don't see a recording on {self._date_label(d)}. "
                "Pick one from the file explorer instead.")
            self._open_picker_and_handle()
            return
        if intent.summarize_all and len(cands) > 1:
            self._summarize_many(cands, self._date_label(d))
            return
        if len(cands) == 1:
            self._start_bg(lambda: self._handle_recording(cands[0]))
            return
        self._pending_pick = cands
        self._append_iris(self._format_pick(
            cands, f"You have {len(cands)} recordings on "
            f"{self._date_label(d)}. Which one?", show="time"))
    def _do_range(self, intent) -> None:
        start, end = intent.date_range
        cands = iq.candidates_for_range(self._all_recordings(), start, end)
        if not cands:
            self._append_iris(
                f"I don't see any recordings between {self._date_label(start)} "
                f"and {self._date_label(end)}.")
            return
        self._summarize_many(
            cands, f"{self._date_label(start)} \u2192 {self._date_label(end)}")
    def _do_index_range(self, intent) -> None:
        a, b = intent.index_range
        base = self._pending_pick if self._pending_pick else \
            sorted(self._all_recordings(), key=iq.rec_dt, reverse=True)
        base = [r for r in base if not iq.is_empty(r)] if not self._pending_pick \
            else base
        sel = base[a - 1:b]
        if not sel:
            self._append_iris(
                f"I only have {len(base)} recordings in that list, so I can't "
                f"reach {a}\u2013{b}. Try a smaller range.")
            return
        self._summarize_many(sel, f"items {a}\u2013{b}")
    def _do_month(self, intent) -> None:
        y, mo, _ = intent.dates[0]
        cands = iq.candidates_for_month(self._all_recordings(), y, mo)
        if not cands:
            self._append_iris(
                f"I don't see any recordings in {self._month_label((y, mo))}. "
                "Pick one from the file explorer instead.")
            self._open_picker_and_handle()
            return
        if intent.summarize_all and len(cands) > 1:
            self._summarize_many(cands, self._month_label((y, mo)))
            return
        if len(cands) == 1:
            self._start_bg(lambda: self._handle_recording(cands[0]))
            return
        self._pending_pick = cands
        self._append_iris(self._format_pick(
            cands, f"You have {len(cands)} recordings in "
            f"{self._month_label((y, mo))}. Which one?", show="date"))
    def _do_time(self, intent) -> None:
        cands = iq.candidates_for_time(self._all_recordings(), intent.time)
        if len(cands) == 1:
            self._start_bg(lambda: self._handle_recording(cands[0]))
            return
        if len(cands) > 1:
            h, mi, s = intent.time
            clock = f"{h:02d}:{mi:02d}" + (f":{s:02d}" if s is not None else "")
            self._pending_pick = cands
            self._append_iris(self._format_pick(
                cands, f"I found {len(cands)} recordings at {clock}. Which one?",
                show="datetime"))
            return
        self._append_iris("I don't see a recording at that time.")
    def _do_content(self, intent) -> None:
        topic = intent.content_query
        hits = iq.content_search(topic, self._all_recordings())
        if not hits:
            self._append_iris(
                f"I couldn't find a recording where you talked about "
                f"\u201c{topic}\u201d. It may not be transcribed yet, or the "
                "topic was phrased differently.")
            return
        if len(hits) == 1:
            rec = hits[0]
            self._append_iris(
                f"That sounds like \u201c{rec.name}\u201d ({rec.when()}). "
                "Pulling it up\u2026")
            self._start_bg(lambda: self._handle_recording(rec))
            return
        self._pending_pick = hits[:30]
        self._append_iris(self._format_pick(
            hits[:30], f"I found {len(hits)} recordings that mention "
            f"\u201c{topic}\u201d. Which one?", show="datetime"))
    # ── picker ───────────────────────────────────────────────────────────
    def _open_picker_and_handle(self) -> None:
        path = self._pick_via_dialog()
        if not path:
            self._append_iris(
                "No file selected. Ask me again and choose a recording from "
                "the picker, or type part of its name or date.")
            return
        rec = self.store.build(path)
        if rec is None:
            self._append_iris("I couldn't read that file.")
            return
        self._start_bg(lambda: self._handle_recording(rec))
    # ── Background runner ────────────────────────────────────────────────
    def _start_bg(self, work) -> None:
        self.busy = True
        self.status_dot.setStyleSheet(
            f"color:{USER_ACCENT}; background:transparent; border:none; font-size:13px;")
        thinking = self._append_iris("\u2026", log=False)
        def run():
            try:
                reply = work()
            except Exception as exc:
                reply = f"(error handling that: {exc})"
            self._call_main(lambda: self._finish_response(thinking, reply))
        threading.Thread(target=run, daemon=True).start()
    def _finish_response(self, thinking_label: QLabel, reply: str) -> None:
        try:
            if reply:
                thinking_label.setText(reply)
            else:
                # Empty reply means the handler (e.g. _capture_via_esp32) already
                # posted its own bubble via _call_main — remove the thinking "…" widget.
                thinking_label.setParent(None)
                thinking_label.deleteLater()
        except Exception:
            pass
        if reply:
            self.history.append({"role": "assistant", "content": reply})
            self._log("assistant", reply)
        self.busy = False
        self.status_dot.setStyleSheet(
            f"color:{ACCENT}; background:transparent; border:none; font-size:13px;")
        QTimer.singleShot(0, self._scroll_to_bottom)
    # ── Recordings access (mirror audio tab, merge duplicate rows) ───────
    def _all_recordings(self) -> list[Recording]:
        gui = self.store.audio_gui
        rows = getattr(gui, "_rows", None) if gui is not None else None
        recs: list[Recording] = []
        if rows:
            recs = [self.store.build(p) for _, p in rows]
            recs = [r for r in recs if r is not None]
        if not recs:
            recs = self.store.list_recent(limit=500)
        return self._merge_dupes(recs)
    @staticmethod
    def _merge_dupes(recs: list[Recording]) -> list[Recording]:
        """Collapse rows that are the same clip (same name, start time, and
        length) into one, preferring the transcribed copy."""
        best: dict = {}
        for r in recs:
            dt = iq.rec_dt(r) if iq is not None else \
                datetime.fromtimestamp(r.mtime)
            key = (r.name.lower(), dt.replace(microsecond=0),
                   round(r.duration_sec) if r.duration_sec else None)
            cur = best.get(key)
            if cur is None or (r.has_transcript and not cur.has_transcript):
                best[key] = r
        return list(best.values())
    def _list_recordings_text(self) -> str:
        recs = [r for r in self._all_recordings() if not iq.is_empty(r)]
        if not recs:
            return ("I don't see any recordings yet \u2014 record one in the "
                    "Audio tab or import a file, and it'll show up here.")
        recs.sort(key=iq.rec_dt, reverse=True)
        self._pending_pick = recs[:30]
        n = len(recs)
        head = (f"I can see {n} recording{'s' if n != 1 else ''}"
                + (" (showing the 30 most recent)" if n > 30 else "") + ":\n")
        lines = [head]
        for i, r in enumerate(self._pending_pick, 1):
            when = iq.rec_dt(r).strftime("%b %d %H:%M")
            mark = "" if r.has_transcript else "  (not transcribed)"
            lines.append(f"  {i}. {r.name} \u00b7 {when} \u00b7 {r.length()}{mark}")
        lines.append("\nReference any by name or date, or reply with its "
                     "number, and I'll pull up its transcript.")
        return "\n".join(lines)
    # ── Pick-list formatting ─────────────────────────────────────────────
    def _format_pick(self, cands, prompt: str, show: str = "time") -> str:
        lines = [prompt + "\n"]
        for i, r in enumerate(cands, 1):
            dt = iq.rec_dt(r)
            if show == "time":
                stamp = dt.strftime("%H:%M:%S")
            elif show == "date":
                stamp = dt.strftime("%b %d %H:%M")
            elif show == "datetime":
                stamp = dt.strftime("%b %d %H:%M:%S")
            else:
                stamp = dt.strftime("%b %d %H:%M")
            mark = "" if r.has_transcript else "  (not transcribed yet)"
            lines.append(f"  {i}. {stamp} \u00b7 {r.name} \u00b7 {r.length()}{mark}")
        lines.append("\nReply with a number, a time like 09:40, or a duration "
                     "like '6 seconds'.")
        return "\n".join(lines)
    def _format_generic_pick(self, cands, prompt: str) -> str:
        return self._format_pick(cands, prompt, show="datetime")
    def _date_label(self, d) -> str:
        y, mo, day = d
        name = [k for k, v in iq.MONTHS.items() if v == mo][0].capitalize()
        return f"{name} {day}" + (f", {y}" if y else "")
    def _month_label(self, mo) -> str:
        year, month = mo
        name = [k for k, v in iq.MONTHS.items() if v == month][0].capitalize()
        return f"{name}" + (f" {year}" if year else "")
    # ── Pick-reply detection + resolution (multi-pick from one list) ─────
    @staticmethod
    def _is_pick_reply(low: str) -> bool:
        if re.search(r"\b(?:option|number|item|no\.?|#)\s*\d{1,3}\b", low):
            return True
        if re.fullmatch(r"\s*#?\d{1,3}\s*", low):
            return True
        if re.search(r"\b\d{1,2}(?:st|nd|rd|th)\b", low):
            return True
        if re.search(r"\b\d{1,3}\s*-?\s*(?:seconds?|secs?|minutes?|mins?)\b", low):
            return True
        if re.search(r"\b\d{1,2}:[0-5]\d(?::[0-5]\d)?\b", low):
            return True
        qwords = ("who", "what", "when", "where", "why", "how", "did", "was",
                  "were", "is", "are", "does", "do", "can", "could", "should")
        if not any(re.search(rf"\b{w}\b", low) for w in qwords):
            if any(re.search(rf"\b{w}\b", low) for w in (
                    "first", "second", "third", "fourth", "fifth", "sixth",
                    "seventh", "eighth", "ninth", "tenth", "earliest",
                    "latest", "newest")):
                return True
            if "most recent" in low or re.search(
                    r"\bthe last (one|recording)\b", low):
                return True
        return False
    def _resolve_pending(self, low: str, cands) -> Optional[Recording]:
        n = len(cands)
        dur = iq.parse_duration(low)
        if dur is not None:
            matches = [r for r in cands if r.duration_sec is not None
                       and round(r.duration_sec) == dur]
            if len(matches) == 1:
                return matches[0]
            if len(matches) > 1:
                return matches[-1]
        idx = self._parse_ordinal(low)
        if idx is not None and 1 <= idx <= n:
            return cands[idx - 1]
        if "earliest" in low:
            return cands[0]
        if ("latest" in low or "most recent" in low
                or re.search(r"\blast\b", low)):
            return cands[-1]
        digits = re.sub(r"[^0-9]", "", low)
        if digits and len(digits) >= 3:
            for r in cands:
                rdt = iq.rec_dt(r)
                hhmmss = f"{rdt.hour:02d}{rdt.minute:02d}{rdt.second:02d}"
                hhmm = f"{rdt.hour:02d}{rdt.minute:02d}"
                if digits in (hhmmss, hhmm) or (len(digits) >= 4
                                                and digits in hhmmss):
                    return r
        idx = self._parse_index(low)
        if idx is not None and 1 <= idx <= n:
            return cands[idx - 1]
        for r in cands:
            stem = os.path.splitext(r.name)[0].lower()
            if stem and (stem in low or low in stem):
                return r
        return None
    @staticmethod
    def _parse_ordinal(low: str) -> Optional[int]:
        words = {"first": 1, "second": 2, "third": 3, "fourth": 4, "fifth": 5,
                 "sixth": 6, "seventh": 7, "eighth": 8, "ninth": 9, "tenth": 10}
        for w, i in words.items():
            if re.search(rf"\b{w}\b", low):
                return i
        m = re.search(r"\b(\d{1,2})(?:st|nd|rd|th)\b", low)
        if m:
            return int(m.group(1))
        return None
    @staticmethod
    def _parse_index(low: str) -> Optional[int]:
        m = re.search(r"\b(?:number|option|item|no\.?|#)\s*(\d{1,3})\b", low)
        if m:
            return int(m.group(1))
        if re.fullmatch(r"\s*#?(\d{1,3})\s*", low):
            return int(re.search(r"\d{1,3}", low).group())
        m = re.search(r"\b(\d{1,3})\b", low)
        if m:
            return int(m.group(1))
        return None
    # ── File picker ──────────────────────────────────────────────────────
    def _recordings_dir(self) -> str:
        named = None
        for d in self.store._candidate_dirs():
            try:
                for fn in os.listdir(d):
                    if Path(fn).suffix.lower() in _AUDIO_EXTS:
                        return d
            except Exception:
                pass
            if named is None and os.path.basename(d).lower() in (
                    "recordings", "recording"):
                named = d
        return named or os.getcwd()
    def _pick_via_dialog(self) -> str:
        try:
            path, _ = QFileDialog.getOpenFileName(
                self, "Select a recording", self._recordings_dir(),
                "Audio files (*.wav *.mp3 *.m4a *.flac *.ogg *.aac *.wma "
                "*.webm *.mp4);;All files (*.*)")
            return path or ""
        except Exception:
            return ""
    # ── Handle a chosen recording ────────────────────────────────────────
    def _handle_recording(self, rec: Recording) -> str:
        self._active = rec
        header = f"\U0001F4FC {rec.name} \u00b7 {rec.length()} \u00b7 {rec.when()}\n\n"
        if rec.has_transcript:
            return self._summarize_recording(rec)
        if rec.duration_sec is not None and rec.duration_sec <= 0:
            return (header + "The audio you selected is zero seconds long, so "
                    "there's nothing I can transcribe. Pick a different "
                    "recording.")
        self._call_main(lambda: self._do_transcribe_ui(rec))
        return (header + "This recording isn't transcribed yet. I've opened the "
                "Audio tab and started transcribing it for you. Once it "
                "finishes, ask me about it again and I'll summarize it.")
    # ── Auto-transcription (GUI thread) ──────────────────────────────────
    _TRANSCRIBE_POLL_MS = 2000
    _TRANSCRIBE_POLL_MAX = 150
    def _do_transcribe_ui(self, rec: Recording) -> None:
        try:
            if self._switch_to_audio is not None:
                self._switch_to_audio()
        except Exception:
            pass
        if self._invoke_audio_transcription(rec):
            if rec.path not in self._polling:
                self._polling.add(rec.path)
                QTimer.singleShot(self._TRANSCRIBE_POLL_MS,
                                  lambda: self._poll_transcription(rec.path, 0))
        else:
            self._append_iris(
                "I couldn't auto-start transcription, but I've taken you to the "
                f"Audio tab \u2014 select \"{rec.name}\" and click the "
                "transcribe button (the third blue button in Recordings).")
    def _poll_transcription(self, path: str, attempts: int) -> None:
        try:
            rec = self.store.build(path)
        except Exception:
            rec = None
        if rec is not None and rec.has_transcript:
            self._polling.discard(path)
            self._active = rec
            self._post_auto_summary(rec)
            return
        if attempts >= self._TRANSCRIBE_POLL_MAX:
            self._polling.discard(path)
            self._append_iris(
                f"Transcription of {os.path.basename(path)} is still running. "
                "Ask me about it once it finishes and I'll summarize it.")
            return
        QTimer.singleShot(self._TRANSCRIBE_POLL_MS,
                          lambda: self._poll_transcription(path, attempts + 1))
    def _post_auto_summary(self, rec: Recording) -> None:
        label = self._append_iris(
            f"\u2705 {rec.name} finished transcribing. Summarizing\u2026")
        def run():
            reply = self._summarize_recording(rec)
            self._call_main(lambda: self._safe_set(label, reply))
        threading.Thread(target=run, daemon=True).start()
    def _safe_set(self, label: QLabel, text: str) -> None:
        try:
            label.setText(text)
        except Exception:
            pass
        self.history.append({"role": "assistant", "content": text})
        self._log("assistant", text)
        QTimer.singleShot(0, self._scroll_to_bottom)
    def _invoke_audio_transcription(self, rec: Recording) -> bool:
        gui = self.store.audio_gui
        if gui is not None:
            try:
                if hasattr(gui, "_select"):
                    gui._select(rec.path)
                else:
                    gui._selected_path = rec.path
                if hasattr(gui, "_on_transcribe_clicked"):
                    gui._on_transcribe_clicked()
                    return True
                ctrl = getattr(gui, "controller", None)
                if ctrl is not None and hasattr(ctrl, "transcribe_file"):
                    ctrl.transcribe_file(rec.path)
                    return True
            except Exception:
                pass
        ctrl = self.store.controller
        if ctrl is not None and hasattr(ctrl, "transcribe_file"):
            try:
                ctrl.transcribe_file(rec.path)
                return True
            except Exception:
                pass
        return False
    # ── Summaries (single + many) ────────────────────────────────────────
    def _summarize_recording(self, rec: Recording) -> str:
        header = f"\U0001F4FC {rec.name} \u00b7 {rec.length()} \u00b7 {rec.when()}\n\n"
        if not rec.has_transcript:
            return (header + "This recording hasn't been transcribed yet. Open "
                    "the Audio tab, select it, and run transcription first.")
        transcript = self._truncate(rec.transcript, 7000)
        if self._client is not None:
            prompt = (
                "Summarize this recording transcript in 3-4 sentences, then "
                "list 2-3 specific follow-up questions the user could ask "
                "about it. Use only what's in the transcript.\n\n"
                f"TRANSCRIPT:\n{transcript}")
            try:
                resp = self._client.chat(
                    model=OLLAMA_MODEL,
                    messages=[{"role": "system", "content": self._system_prompt},
                              {"role": "user", "content": prompt}])
                return header + resp["message"]["content"].strip()
            except Exception as exc:
                if rec.summary:
                    return header + rec.summary
                return (header + f"(couldn't reach the model: {exc})\n\n"
                        "Transcript excerpt:\n" + self._truncate(rec.transcript, 800))
        if rec.summary:
            return header + rec.summary
        return header + "Transcript excerpt:\n" + self._truncate(rec.transcript, 800)
    def _summarize_many(self, recs, label: str) -> None:
        recs = [r for r in recs if not iq.is_empty(r)]
        if not recs:
            self._append_iris(f"I don't see any recordings for {label}.")
            return
        capped = recs[:8]
        note = "" if len(recs) <= 8 else f" (first 8 of {len(recs)})"
        self._start_bg(
            lambda: self._do_summarize_many(capped, label, note))
    def _do_summarize_many(self, recs, label: str, note: str) -> str:
        header = f"\U0001F4CA {label}{note} \u2014 {len(recs)} recording(s)\n\n"
        transcribed = [r for r in recs if r.has_transcript]
        missing = [r for r in recs if not r.has_transcript]
        if not transcribed:
            lines = [header + "None of these are transcribed yet:"]
            for r in recs:
                lines.append(f"  \u2022 {r.name} \u00b7 {r.when()} \u00b7 {r.length()}")
            lines.append("\nOpen one and I'll transcribe it, then summarize.")
            return "\n".join(lines)
        if self._client is None:
            lines = [header]
            for r in transcribed:
                s = r.summary or self._truncate(r.transcript, 200)
                lines.append(f"\u2022 {r.name} ({r.when()}): {s}")
            return "\n".join(lines)
        blocks = []
        for r in transcribed:
            blocks.append(f"=== {r.name} ({r.when()}, {r.length()}) ===\n"
                          + self._truncate(r.transcript, 2500))
        prompt = (
            "Summarize each of the following recordings in 1-2 sentences, "
            "labeled by file name, then finish with a short overall takeaway "
            "across all of them. Use only what's in each transcript.\n\n"
            + "\n\n".join(blocks))
        try:
            resp = self._client.chat(
                model=OLLAMA_MODEL,
                messages=[{"role": "system", "content": self._system_prompt},
                          {"role": "user", "content": prompt}])
            out = header + resp["message"]["content"].strip()
        except Exception as exc:
            out = header + f"(couldn't reach the model: {exc})"
        if missing:
            out += ("\n\n(Not transcribed yet: "
                    + ", ".join(r.name for r in missing) + ")")
        return out
    # ── Follow-up about the active recording (incl. timestamp / topic) ───
    _RECORDING_Q_WORDS = (
        "summar", "transcript", "recording", "what did", "what was",
        "who said", "who is", "who was", "what happened", "talk about",
        "talked about", "discuss", "mention", "meeting", "the call",
        "this call", "what's in", "whats in", "recap", "time frame",
        "timeframe", "what time", "when did", "they said", "conversation",
    )
    def _is_about_recording(self, low: str) -> bool:
        if any(k in low for k in self._RECORDING_Q_WORDS):
            return True
        return len(low.split()) <= 4
    def _topic_from_question(self, text: str) -> str:
        topic = iq.extract_topic(text) if iq is not None else ""
        if topic:
            return topic
        low = text.lower()
        low = re.sub(r"[?.!,]", " ", low)
        drop = {"when", "what", "time", "where", "did", "we", "i", "you", "the",
                "a", "an", "at", "point", "in", "this", "recording", "talk",
                "talked", "about", "discuss", "discussed", "mention",
                "mentioned", "was", "is", "of", "do", "does", "happen", "say",
                "said", "happened"}
        toks = [t for t in re.split(r"\s+", low) if t and t not in drop
                and len(t) >= 3]
        return " ".join(toks)
    def _answer_followup(self, text: str) -> str:
        low = text.lower().strip()
        rec = self._active
        if rec is not None:
            try:
                fresh = self.store.build(rec.path)
                if fresh is not None:
                    self._active = rec = fresh
            except Exception:
                pass
        # "this/that photo", "when was it taken" — answered from metadata
        # only; there's no vision model wired into chat to describe content.
        if self._active_photo is not None and re.search(
                r"\b(this|that|the)\s+(photo|picture|screenshot|pic|image)\b"
                r"|\bwhen\s+(was\s+)?(it|this|that)\s+(taken|captured)\b"
                r"|\bhow\s+(was\s+)?(it|this|that)\s+(taken|captured)\b",
                low):
            p = self._active_photo
            tag = _photo_source_label(p.source, verbose=True)
            msg = f"That photo was taken {p.when()}, captured {tag}"
            if p.trigger_text:
                msg += f" (triggered by \u201c{p.trigger_text}\u201d)"
            msg += (". I can't see what's actually in the image \u2014 no "
                    "vision model is connected to chat yet \u2014 but I can "
                    "tell you when or how anything was captured.")
            return msg
        # "what was said at 5:30" / "around 1:20"
        m = re.search(r"\b(?:at|around|near|by|@)\s*(\d{1,2}):([0-5]\d)\b", low)
        if rec is not None and m:
            secs = int(m.group(1)) * 60 + int(m.group(2))
            head = f"\U0001F4FC {rec.name}\n\n"
            if rec.segments:
                seg = iq.lookup_offset(rec, secs)
                if seg is not None:
                    spk = seg.get("speaker")
                    who = f"{spk}: " if spk else ""
                    return (head + f"Around {iq.fmt_offset(secs)} \u2014 "
                            + who + seg.get("text", "").strip())
                return (head + f"This recording is only {rec.length()} long, so "
                        f"there's nothing at {iq.fmt_offset(secs)}.")
            return (head + "This recording doesn't have timestamped segments, "
                    f"so I can't pin down exactly what was said at "
                    f"{iq.fmt_offset(secs)}.")
        # "when did we talk about X" / "where is X mentioned"
        if rec is not None and re.search(
                r"\b(when|what time|where|at what point)\b", low):
            topic = self._topic_from_question(text)
            if topic:
                hits = iq.find_topic_in_recording(topic, rec)
                if hits:
                    lines = [f"\U0001F4FC {rec.name} \u2014 \u201c{topic}\u201d "
                             "comes up here:"]
                    for start, spk, txt in hits[:4]:
                        when = (iq.fmt_offset(start) if start is not None
                                else "?")
                        who = f"{spk}: " if spk else ""
                        snippet = txt if len(txt) <= 160 else txt[:157] + "\u2026"
                        lines.append(f"  \u2022 {when} \u2014 {who}{snippet}")
                    if not rec.segments:
                        lines.append("\n(This recording has no per-line "
                                     "timestamps, so I can only show the lines.)")
                    return "\n".join(lines)
                return (f"I don't see \u201c{topic}\u201d mentioned in "
                        f"{rec.name}.")
        if (rec is not None and not rec.has_transcript
                and self._is_about_recording(low)):
            return (f"\U0001F4FC {rec.name} isn't transcribed yet, so I can't "
                    "answer from it. It's transcribing now \u2014 I'll post the "
                    "summary automatically when it's ready, or ask again in a "
                    "moment.")
        return self._ask_ollama(text)
    def _active_context_block(self) -> Optional[str]:
        if not self._active or not self._active.has_transcript:
            return None
        return (f"The user is asking about this recording:\n"
                f"name: {self._active.name}\n"
                f"recorded: {self._active.when()}  length: {self._active.length()}\n"
                f"TRANSCRIPT:\n{self._truncate(self._active.transcript, 7000)}")
    @staticmethod
    def _truncate(text: str, limit: int) -> str:
        text = (text or "").strip()
        if len(text) <= limit:
            return text
        return text[:limit].rsplit(" ", 1)[0] + " \u2026[truncated]"
    def _ask_ollama(self, _text: str) -> str:
        if self._client is None:
            return "(ollama not connected)"
        messages = [{"role": "system", "content": self._system_prompt}]
        ctx = self._active_context_block()
        if ctx:
            messages.append({"role": "system", "content": ctx})
        messages.extend(self.history)
        try:
            resp = self._client.chat(model=OLLAMA_MODEL, messages=messages)
            return resp["message"]["content"].strip()
        except Exception as exc:
            return f"(ollama error: {exc})"
# ─────────────────────────────────────────────────────────────────────────────
# Placeholder tabs (glass)
# ─────────────────────────────────────────────────────────────────────────────
class PlaceholderTab(QWidget):
    def __init__(self, parent, title: str, items: list[str], milestone: str):
        super().__init__(parent)
        outer = QVBoxLayout(self)
        outer.addStretch(1)
        card = GlassFrame(self, radius=18, blur=30, dy=8)
        card.setMaximumWidth(460)
        cl = QVBoxLayout(card)
        cl.setContentsMargins(28, 24, 28, 26)
        cl.setSpacing(2)
        t = QLabel(title)
        t.setStyleSheet(
            f"color:{TEXT_PRIMARY}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:18px; font-weight:700;")
        cl.addWidget(t)
        ms = QLabel(f"arrives in {milestone}")
        ms.setStyleSheet(
            f"color:{ACCENT}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:11px; padding-bottom:10px;")
        cl.addWidget(ms)
        for item in items:
            it = QLabel(f"\u00b7  {item}")
            it.setStyleSheet(
                f"color:{TEXT_MUTED}; background:transparent; border:none;"
                f"font-family:'{FONT_SANS}'; font-size:11px; padding:1px 0;")
            cl.addWidget(it)
        wrap = QHBoxLayout()
        wrap.addStretch(1)
        wrap.addWidget(card)
        wrap.addStretch(1)
        outer.addLayout(wrap)
        outer.addStretch(2)
# ─────────────────────────────────────────────────────────────────────────────
# Audio dashboard — glass Qt port of gui_phase9.AudioStreamGUI, embedded in the
# same window (no popup). Drives the same Controller + speaker_db + event_queue.
# ─────────────────────────────────────────────────────────────────────────────
def _audio_btn(text: str, on_click=None, *, fg: str = TEXT_PRIMARY,
               accent: str = "255,255,255", height: int = 36,
               bold: bool = False, width: Optional[int] = None) -> QPushButton:
    b = QPushButton(text)
    b.setCursor(Qt.CursorShape.PointingHandCursor)
    if height:
        b.setFixedHeight(height)
    if width:
        b.setFixedWidth(width)
    weight = "700" if bold else "500"
    b.setStyleSheet(
        "QPushButton {"
        f"color:{fg}; background: rgba({accent},0.12);"
        f"border: 1px solid rgba({accent},0.30); border-radius: 10px;"
        "padding: 0 12px;"
        f"font-family:'{FONT_SANS}'; font-size:12px; font-weight:{weight};"
        "}"
        f"QPushButton:hover {{ background: rgba({accent},0.20); }}")
    if on_click:
        b.clicked.connect(on_click)
    _add_glass_shadow(b, blur=12, dy=2, alpha=90)
    return b
class VUMeter(QWidget):
    """Segmented input-level meter with a falling peak hold."""
    def __init__(self):
        super().__init__()
        self.setMinimumHeight(22)
        self._level = 0.0
        self._peak = 0.0
    def setLevel(self, lvl: float) -> None:
        lvl = max(0.0, min(1.0, lvl))
        self._level = lvl
        self._peak = lvl if lvl > self._peak else max(lvl, self._peak * 0.92)
        self.update()
    def paintEvent(self, _evt):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(255, 255, 255, 16))
        p.drawRoundedRect(0, 0, w, h, 6, 6)
        seg = 30
        sw = w / seg
        for i in range(seg):
            frac = i / seg
            if frac > self._level:
                col = QColor(255, 255, 255, 28)
            elif frac > 0.85:
                col = QColor("#ef4444")
            elif frac > 0.7:
                col = QColor("#f59e0b")
            else:
                col = QColor("#10b981")
            x0 = int(i * sw) + 2
            x1 = int((i + 1) * sw) - 1
            p.setBrush(col)
            p.drawRect(x0, 3, max(1, x1 - x0), h - 6)
        if self._peak > 0.02:
            px = int(self._peak * w)
            p.setBrush(QColor("#ffffff"))
            p.drawRect(max(0, px - 2), 2, 2, h - 4)
class StatusDot(QWidget):
    """Coloured dot + label, e.g. '\u25cf Audio stream: receiving'."""
    def __init__(self, text: str):
        super().__init__()
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(6)
        self._dot = QLabel("\u25CF")
        self._dot.setStyleSheet(
            f"color:{COLOR_STATUS_OFF}; background:transparent; border:none;"
            "font-size:13px; font-weight:700;")
        self._label = QLabel(text)
        self._label.setStyleSheet(
            f"color:{TEXT_MUTED}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:12px;")
        lay.addWidget(self._dot)
        lay.addWidget(self._label)
        lay.addStretch(1)
    def set(self, *, on: bool = False, text: Optional[str] = None,
            color: Optional[str] = None) -> None:
        c = color if color else (COLOR_STATUS_ON if on else COLOR_STATUS_OFF)
        self._dot.setStyleSheet(
            f"color:{c}; background:transparent; border:none;"
            "font-size:13px; font-weight:700;")
        if text is not None:
            self._label.setText(text)
class ManageSpeakersDialog(QDialog):
    """Port of gui_phase9.ManageSpeakersDialog \u2014 list / rename / delete."""
    def __init__(self, parent, speaker_db, recordings_dir, on_changed):
        super().__init__(parent)
        self.setWindowTitle("Manage Speaker Profiles")
        self.resize(560, 480)
        self.setStyleSheet(
            f"QDialog {{ background:{BG_MID}; }}"
            f"QLabel {{ color:{TEXT_PRIMARY}; font-family:'{FONT_SANS}'; }}")
        self._db = speaker_db
        self._dir = recordings_dir
        self._on_changed = on_changed
        self._root = QVBoxLayout(self)
        self._build()
    def _build(self):
        while self._root.count():
            item = self._root.takeAt(0)
            w = item.widget()
            if w:
                w.deleteLater()
        title = QLabel("\U0001F464  Saved Speaker Profiles")
        title.setStyleSheet(f"color:{TEXT_PRIMARY}; font-size:16px;"
                            "font-weight:700;")
        self._root.addWidget(title)
        try:
            profiles = self._db.all_info() if self._db else []
        except Exception:
            profiles = []
        if not profiles:
            note = QLabel("No speakers enrolled yet. Tag a speaker in a "
                          "transcript to enroll them.")
            note.setWordWrap(True)
            note.setStyleSheet(f"color:{TEXT_MUTED}; font-size:12px;")
            self._root.addWidget(note)
            self._root.addStretch(1)
            self._root.addWidget(_audio_btn("Close", self.accept,
                                            accent=_rgb(ACCENT), fg=ACCENT,
                                            width=100),
                                 0, Qt.AlignmentFlag.AlignRight)
            return
        counts = self._count_appearances()
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setStyleSheet("background: transparent;")
        holder = QWidget()
        holder.setStyleSheet("background: transparent;")
        vl = QVBoxLayout(holder)
        vl.setContentsMargins(0, 0, 0, 0)
        vl.setSpacing(6)
        for info in profiles:
            card = GlassFrame(holder, radius=10, blur=14, dy=3, shadow_alpha=90)
            cl = QHBoxLayout(card)
            cl.setContentsMargins(12, 8, 10, 8)
            txt = QVBoxLayout()
            nm = QLabel(info.get("name", "?"))
            nm.setStyleSheet(f"color:{TEXT_PRIMARY}; font-size:13px;"
                             "font-weight:700;")
            appears = counts.get(info.get("name"), 0)
            sc = info.get("sample_count", 0)
            sub = QLabel(f"{sc} voice sample{'s' if sc != 1 else ''}  \u2022  "
                         f"appears in {appears} recording"
                         f"{'s' if appears != 1 else ''}")
            sub.setStyleSheet(f"color:{TEXT_DIM}; font-size:10px;")
            txt.addWidget(nm)
            txt.addWidget(sub)
            cl.addLayout(txt, 1)
            cl.addWidget(_audio_btn("Rename",
                                    lambda _=False, n=info["name"]: self._rename(n),
                                    accent=_rgb(BADGE_VOICE_FG),
                                    fg=BADGE_VOICE_FG, width=80, height=30))
            cl.addWidget(_audio_btn("Delete",
                                    lambda _=False, n=info["name"]: self._delete(n),
                                    accent=_rgb(COLOR_DANGER),
                                    fg="#fca5a5", width=80, height=30))
            vl.addWidget(card)
        vl.addStretch(1)
        scroll.setWidget(holder)
        self._root.addWidget(scroll, 1)
        self._root.addWidget(_audio_btn("Close", self.accept,
                                        accent=_rgb(ACCENT), fg=ACCENT,
                                        width=100),
                             0, Qt.AlignmentFlag.AlignRight)
    def _count_appearances(self) -> dict:
        counts: dict = {}
        try:
            for jp in glob.glob(os.path.join(self._dir, "recording_*.json")):
                try:
                    with open(jp, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    names = {seg.get("speaker") for seg in data.get("segments", [])
                             if seg.get("speaker")}
                    for n in names:
                        counts[n] = counts.get(n, 0) + 1
                except Exception:
                    pass
        except Exception:
            pass
        return counts
    def _rename(self, old: str):
        from PyQt6.QtWidgets import QInputDialog
        new, ok = QInputDialog.getText(self, "Rename Speaker",
                                       f"New name for \"{old}\":", text=old)
        new = new.strip() if ok else ""
        if not new or new == old:
            return
        try:
            self._db.rename(old, new)
        except Exception:
            pass
        self._rename_in_transcripts(old, new)
        self._on_changed()
        self._build()
    def _rename_in_transcripts(self, old: str, new: str):
        for jp in glob.glob(os.path.join(self._dir, "recording_*.json")):
            try:
                with open(jp, "r", encoding="utf-8") as f:
                    data = json.load(f)
                changed = False
                for seg in data.get("segments", []):
                    if seg.get("speaker") == old:
                        seg["speaker"] = new
                        changed = True
                if changed:
                    with open(jp, "w", encoding="utf-8") as f:
                        json.dump(data, f, indent=2)
            except Exception:
                pass
    def _delete(self, name: str):
        from PyQt6.QtWidgets import QMessageBox
        r = QMessageBox.question(
            self, "Confirm Delete",
            f"Delete \"{name}\" and all their voice samples?\n"
            "Transcript labels using this name will remain.")
        if r != QMessageBox.StandardButton.Yes:
            return
        try:
            self._db.delete(name)
        except Exception:
            pass
        self._on_changed()
        self._build()
class AudioTab(QWidget):
    """Embedded glass audio dashboard. Names like _select / _on_transcribe_clicked
    match the chat tab's auto-transcribe hook so it drives this tab directly."""
    poll_signal = pyqtSignal()
    def __init__(self, parent, controller, app_config, location_tab=None,
                 switch=None):
        super().__init__(parent)
        self.controller = controller
        self.cfg = app_config
        self.location_tab = location_tab
        self._selected_path: Optional[str] = None
        self._rows: list[tuple[QPushButton, str]] = []
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        # Live wake-word listener state. See _on_live_transcribe_clicked.
        self._wake_active = False
        self._wake_dir: Optional[str] = None
        self._wake_counter = 0
        self._wake_cooldown_until = 0.0
        self._wake_callback = None
        self._wake_owns_mic = False          # did we start the PC mic capture?
        self._wake_last_text = None          # last chunk shown (light dedup)
        self._wake_last_peek_ts = 0.0        # for adaptive window sizing
        # Without a backend, show a glass notice instead of crashing.
        if controller is None or app_config is None:
            self._build_notice()
            return
        self._build()
        self._bind_hotkeys()
        self._start_timers()
        self._refresh_recordings()
        if self.location_tab is not None:
            self.location_tab.refresh()
    # ---- config access with safe defaults ----
    def _c(self, attr, default):
        return getattr(self.cfg, attr, default) if self.cfg else default
    # ---- fallback notice (no backend) ----
    def _build_notice(self):
        outer = QVBoxLayout(self)
        outer.addStretch(1)
        card = GlassFrame(self, radius=18, blur=30, dy=8)
        card.setMaximumWidth(520)
        cl = QVBoxLayout(card)
        cl.setContentsMargins(28, 24, 28, 26)
        t = QLabel("audio dashboard")
        t.setStyleSheet(f"color:{TEXT_PRIMARY}; background:transparent;"
                        f"border:none; font-family:'{FONT_SANS}';"
                        "font-size:18px; font-weight:700;")
        note = QLabel("The audio backend isn't loaded. Run iris_gui.py from the "
                      "project folder so config_phase9 and main_phase9 are "
                      "importable, and the full dashboard appears here.")
        note.setWordWrap(True)
        note.setStyleSheet(f"color:{TEXT_MUTED}; background:transparent;"
                           f"border:none; font-family:'{FONT_SANS}';"
                           "font-size:12px;")
        cl.addWidget(t)
        cl.addWidget(note)
        wrap = QHBoxLayout()
        wrap.addStretch(1); wrap.addWidget(card); wrap.addStretch(1)
        outer.addLayout(wrap)
        outer.addStretch(2)
    # ---- layout: 2x2 glass grid ----
    def _build(self):
        grid = QGridLayout(self)
        grid.setContentsMargins(0, 0, 0, 0)
        grid.setHorizontalSpacing(12)
        grid.setVerticalSpacing(12)
        grid.setColumnStretch(0, 2)
        grid.setColumnStretch(1, 3)
        grid.setRowStretch(0, 1)
        grid.setRowStretch(1, 1)
        grid.addWidget(self._panel(self._build_status_panel()), 0, 0)
        grid.addWidget(self._panel(self._build_recordings_panel()), 1, 0)
        # Transcript spans both rows -> fills the entire right half.
        grid.addWidget(self._panel(self._build_transcript_panel()), 0, 1, 2, 1)
    def _panel(self, inner: QWidget) -> QWidget:
        frame = GlassFrame(self, radius=16, blur=24, dy=6, shadow_alpha=120,
                           top="rgba(255,255,255,0.06)",
                           mid="rgba(255,255,255,0.035)",
                           bot="rgba(255,255,255,0.02)",
                           border=GLASS_BORDER_SOFT)
        lay = QVBoxLayout(frame)
        lay.setContentsMargins(14, 12, 14, 12)
        lay.addWidget(inner)
        return frame
    def _h(self, text: str) -> QLabel:
        lbl = QLabel(text)
        lbl.setStyleSheet(f"color:{TEXT_PRIMARY}; background:transparent;"
                          f"border:none; font-family:'{FONT_SANS}';"
                          "font-size:15px; font-weight:700;")
        return lbl
    # ---- status panel ----
    def _build_status_panel(self) -> QWidget:
        w = QWidget(); w.setStyleSheet("background: transparent;")
        scroll = QScrollArea(); scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setStyleSheet(
            "QScrollArea{background:transparent;border:none;}"
            "QScrollBar:vertical{width:8px;background:transparent;}"
            "QScrollBar::handle:vertical{background:rgba(255,255,255,0.14);"
            "border-radius:4px;}")
        scroll.setWidget(w)
        lay = QVBoxLayout(w)
        lay.setContentsMargins(0, 0, 6, 0)
        lay.setSpacing(6)
        lay.addWidget(self._h("Status"))
        self.dot_wifi = StatusDot("Wi-Fi: waiting for ESP32")
        self.dot_stream = StatusDot("Audio stream: idle")
        self.dot_monitor = StatusDot("Monitoring: off")
        self.dot_location = StatusDot("Location: fetching\u2026")
        self.dot_wake = StatusDot("Live transcription: off")
        for d in (self.dot_wifi, self.dot_stream, self.dot_monitor,
                  self.dot_location, self.dot_wake):
            lay.addWidget(d)
        cap = QLabel("Input level")
        cap.setStyleSheet(f"color:{TEXT_DIM}; background:transparent;"
                          f"border:none; font-family:'{FONT_SANS}'; font-size:11px;")
        lay.addSpacing(6)
        lay.addWidget(cap)
        self.vu = VUMeter()
        lay.addWidget(self.vu)
        self.btn_record = _audio_btn("\u25CF  Start Recording",
                                     self._on_record_clicked,
                                     accent=_rgb(COLOR_DANGER), fg="#fca5a5",
                                     height=46, bold=True)
        self.btn_monitor = _audio_btn("\U0001F50A  Start Monitoring",
                                      self._on_monitor_clicked, height=40)
        self.btn_wake = _audio_btn("\U0001F399  Start Live Transcription",
                                   self._on_live_transcribe_clicked, height=40)
        self.btn_manage = _audio_btn("\U0001F464  Manage Speakers",
                                     self._open_manage_speakers, height=36)
        lay.addSpacing(4)
        lay.addWidget(self.btn_record)
        lay.addWidget(self.btn_monitor)
        lay.addWidget(self.btn_wake)
        lay.addWidget(self.btn_manage)
        # Queue / stats grid
        grid = QGridLayout()
        grid.setContentsMargins(0, 8, 0, 0)
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(2)
        rows = [
            ("Recording:", "lbl_rec_duration", "--:--"),
            ("Chunk:", "lbl_rec_chunk", "--"),
            ("Transcribe queue:", "lbl_queue", "0"),
            ("Diarize queue:", "lbl_diarize_queue", "0"),
            ("Summarize queue:", "lbl_sum_queue", "0"),
            ("Packet loss:", "lbl_loss", "--"),
        ]
        for i, (label, attr, default) in enumerate(rows):
            k = QLabel(label)
            k.setStyleSheet(f"color:{TEXT_DIM}; background:transparent;"
                            f"border:none; font-family:'{FONT_SANS}'; font-size:11px;")
            v = QLabel(default)
            v.setStyleSheet(f"color:{TEXT_PRIMARY}; background:transparent;"
                            f"border:none; font-family:'{FONT_MONO}','Consolas',"
                            "monospace; font-size:11px; font-weight:700;")
            grid.addWidget(k, i, 0, Qt.AlignmentFlag.AlignLeft)
            grid.addWidget(v, i, 1, Qt.AlignmentFlag.AlignLeft)
            setattr(self, attr, v)
        holder = QWidget(); holder.setStyleSheet("background:transparent;")
        holder.setLayout(grid)
        lay.addWidget(holder)
        lay.addStretch(1)
        return scroll
    # ---- transcript panel ----
    def _build_transcript_panel(self) -> QWidget:
        w = QWidget(); w.setStyleSheet("background: transparent;")
        lay = QVBoxLayout(w)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(6)
        head = QHBoxLayout()
        head.addWidget(self._h("Transcript"))
        head.addStretch(1)
        self.lbl_transcript_target = QLabel("(no recording selected)")
        self.lbl_transcript_target.setStyleSheet(
            f"color:{TEXT_DIM}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:11px;")
        head.addWidget(self.lbl_transcript_target)
        lay.addLayout(head)
        sh = QLabel("Summary")
        sh.setStyleSheet(f"color:{TEXT_MUTED}; background:transparent;"
                         f"border:none; font-family:'{FONT_SANS}'; font-size:13px;"
                         "font-weight:700;")
        lay.addWidget(sh)
        self.txt_summary = self._textbox(read_only=True, mono=False)
        self.txt_summary.setFixedHeight(150)
        lay.addWidget(self.txt_summary)

        # Transcript (rolling chunks)
        self.txt_transcript = self._textbox(read_only=True, mono=True)
        lay.addWidget(self.txt_transcript, 1)

        # Bottom-right live “together” transcript (accumulates across peeks)
        # This matches what you asked for: keep adding the current words after
        # the previous ones so "hey" + "jarvis" becomes "hey jarvis".
        together_hdr = QLabel("Live (together)")
        together_hdr.setStyleSheet(
            f"color:{TEXT_MUTED}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:13px; font-weight:700;")
        lay.addWidget(together_hdr)

        # Per-start live transcript tabs (new panel per live session).
        # Each click on "Start Live Transcription" creates a new tab and
        # appends/updates text only in that tab.
        from PyQt6.QtWidgets import QTabWidget
        self.live_together_tabs = QTabWidget()
        self.live_together_tabs.setStyleSheet(
            "QTabWidget::pane { border: 1px solid "
            f"{GLASS_BORDER_SOFT}; border-radius: 10px; "
            "background: rgba(255,255,255,0.04); }"
            "QTabBar::tab { color: " + TEXT_MUTED + "; padding: 6px 10px; "
            "border: 1px solid rgba(255,255,255,0.10); border-radius: 8px; "
            "background: rgba(255,255,255,0.02); margin-right: 6px; }"
            "QTabBar::tab:selected { color: " + TEXT_PRIMARY + "; "
            "background: rgba(255,255,255,0.10); }")
        self.live_together_tabs.setFixedHeight(130)
        lay.addWidget(self.live_together_tabs)

        # Set per session in _start_live_transcription()
        self.txt_live_together = None

        btns = QHBoxLayout()
        btns.addWidget(_audio_btn("\U0001F464 Tag Speaker",
                                  self._on_tag_speaker_manual, height=30))
        btns.addStretch(1)
        btns.addWidget(_audio_btn("\u21bb Re-summarize",
                                  self._on_resummarize, height=30,
                                  accent=_rgb(ACCENT), fg=ACCENT))
        # Live summarization button for the accumulated WAV created from
        # live snippets (auto-summarize also runs on stop).
        btns.addWidget(_audio_btn("\u25A0 Summarize Live",
                                  self._on_summarize_live_clicked, height=30,
                                  accent=_rgb(BADGE_FACE_FG), fg=BADGE_FACE_FG,
                                  width=140))
        lay.addLayout(btns)
        return w
    def _textbox(self, read_only: bool, mono: bool) -> QTextEdit:
        t = QTextEdit()
        t.setReadOnly(read_only)
        fam = (f"'{FONT_MONO}','Consolas',monospace" if mono
               else f"'{FONT_SANS}'")
        t.setStyleSheet(
            "QTextEdit {"
            f"color:{TEXT_PRIMARY}; background: rgba(255,255,255,0.04);"
            f"border: 1px solid {GLASS_BORDER_SOFT}; border-radius: 10px;"
            f"padding: 8px; font-family:{fam}; font-size:12px;"
            "}"
            "QScrollBar:vertical{width:8px;background:transparent;}"
            "QScrollBar::handle:vertical{background:rgba(255,255,255,0.14);"
            "border-radius:4px;}")
        return t
    # ---- recordings panel ----
    def _build_recordings_panel(self) -> QWidget:
        w = QWidget(); w.setStyleSheet("background: transparent;")
        lay = QVBoxLayout(w)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(6)
        head = QHBoxLayout()
        head.addWidget(self._h("Recordings"))
        head.addStretch(1)
        for text, cmd in [("\u21bb", self._refresh_all),
                          ("\u25B6", self._on_play_clicked),
                          ("\U0001F4DD", self._on_transcribe_clicked),
                          ("\U0001F4C2", self._on_open_folder),
                          ("\u2B06", self._on_import_file)]:
            head.addWidget(_audio_btn(text, cmd, width=36, height=32,
                                      accent=_rgb(ACCENT), fg=ACCENT))
        lay.addLayout(head)
        scroll = QScrollArea(); scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setStyleSheet(
            "QScrollArea{background:transparent;border:none;}"
            "QScrollBar:vertical{width:8px;background:transparent;}"
            "QScrollBar::handle:vertical{background:rgba(255,255,255,0.14);"
            "border-radius:4px;}")
        self._list_holder = QWidget()
        self._list_holder.setStyleSheet("background: transparent;")
        self._list_lay = QVBoxLayout(self._list_holder)
        self._list_lay.setContentsMargins(0, 0, 6, 0)
        self._list_lay.setSpacing(2)
        self._list_lay.addStretch(1)
        scroll.setWidget(self._list_holder)
        lay.addWidget(scroll, 1)
        return w
    # ---- hotkeys (scoped to this tab so they don't hijack chat input) ----
    def _bind_hotkeys(self):
        binds = {"R": self._on_record_clicked, "M": self._on_monitor_clicked,
                 "P": self._on_play_clicked, "T": self._on_transcribe_clicked}
        for key, fn in binds.items():
            sc = QShortcut(QKeySequence(key), self)
            sc.setContext(Qt.ShortcutContext.WidgetWithChildrenShortcut)
            sc.activated.connect(fn)
    # ---- timers (replace tkinter after-loops) ----
    def _start_timers(self):
        self._evt_timer = QTimer(self)
        self._evt_timer.timeout.connect(self._poll_events)
        self._evt_timer.start(int(self._c("GUI_POLL_MS", 100)))
        self._vu_timer = QTimer(self)
        self._vu_timer.timeout.connect(self._poll_vu)
        self._vu_timer.start(int(self._c("GUI_VU_DECAY_MS", 50)))
    def _poll_events(self):
        if self.controller is None:
            return
        try:
            while True:
                evt = self.controller.event_queue.get_nowait()
                self._handle_event(evt)
        except queue.Empty:
            pass
        except Exception:
            pass
    def _poll_vu(self):
        try:
            self.vu.setLevel(self.controller.peek_level())
        except Exception:
            pass
    def _handle_event(self, evt: dict):
        et = evt.get("type")
        if et == "esp32_connected":
            self.dot_stream.set(on=True, text="Audio stream: receiving")
            self.dot_wifi.set(on=True, text="Wi-Fi: ESP32 connected")
        elif et == "recording_started":
            self.btn_record.setText("\u25A0  Stop Recording")
            self.dot_stream.set(color=COLOR_RECORDING,
                                text=f"RECORDING ({evt.get('session', '')})")
        elif et == "recording_stopped":
            self.btn_record.setText("\u25CF  Start Recording")
            self.dot_stream.set(on=True, text="Audio stream: receiving")
            self.lbl_rec_duration.setText("--:--")
            self.lbl_rec_chunk.setText("--")
            self._refresh_all()
        elif et == "recording_tick":
            m, s = divmod(int(evt.get("duration", 0.0)), 60)
            self.lbl_rec_duration.setText(f"{m:02d}:{s:02d}")
            self.lbl_rec_chunk.setText(str(evt.get("chunk", "--")))
        elif et == "monitor_started":
            self.btn_monitor.setText("\U0001F507  Stop Monitoring")
            self.dot_monitor.set(on=True, text="Monitoring: on")
        elif et == "monitor_stopped":
            self.btn_monitor.setText("\U0001F50A  Start Monitoring")
            self.dot_monitor.set(on=False, text="Monitoring: off")
        elif et == "chunk_finalized":
            self._refresh_all()
        elif et in ("transcribe_done", "diarize_done", "summary_done"):
            self._refresh_recordings()
            if self._selected_path == evt.get("wav"):
                self._show_content(self._selected_path)
        elif et == "transcribe_queue":
            self.lbl_queue.setText(str(evt.get("depth", 0)))
        elif et == "diarize_queue":
            self.lbl_diarize_queue.setText(str(evt.get("depth", 0)))
        elif et == "summarize_queue":
            self.lbl_sum_queue.setText(str(evt.get("depth", 0)))
        elif et == "net_stats":
            self.lbl_loss.setText(f"{evt.get('loss_pct', 0.0):.2f}%")
        elif et == "location_ready":
            loc = evt.get("location")
            if loc:
                place = f"{loc['city']}, {loc['region']}"
                self.dot_location.set(on=True, text=f"Location: {place}")
                if self.location_tab is not None:
                    self.location_tab.set_location(loc)
            else:
                self.dot_location.set(on=False, text="Location: unavailable")
    # ---- button handlers (same Controller calls as gui_phase9) ----
    def _on_record_clicked(self):
        try: self.controller.toggle_recording()
        except Exception: pass
    def _on_monitor_clicked(self):
        try: self.controller.toggle_monitoring()
        except Exception: pass
    def _on_play_clicked(self):
        if self._selected_path:
            try: self.controller.play_file(self._selected_path)
            except Exception: pass
    def _on_transcribe_clicked(self):
        if self._selected_path:
            try: self.controller.transcribe_file(self._selected_path)
            except Exception: pass
    def _on_resummarize(self):
        if self._selected_path:
            try: self.controller.summarize_file(self._selected_path)
            except Exception: pass
    def _on_open_folder(self):
        try:
            os.startfile(self._c("RECORDINGS_DIR", os.getcwd()))  # type: ignore
        except Exception:
            pass
    def _on_import_file(self):
        paths, _ = QFileDialog.getOpenFileNames(
            self, "Import audio files", self._c("RECORDINGS_DIR", os.getcwd()),
            "WAV files (*.wav);;All files (*.*)")
        if not paths:
            return
        imported = 0
        dest = self._c("RECORDINGS_DIR", os.getcwd())
        for src in paths:
            dst = os.path.join(dest, os.path.basename(src))
            if os.path.abspath(src) != os.path.abspath(dst):
                try:
                    shutil.copy2(src, dst); imported += 1
                except Exception:
                    pass
        if imported:
            self._refresh_recordings()
    def _open_manage_speakers(self):
        try:
            ManageSpeakersDialog(self, self.controller.speaker_db,
                                 self._c("RECORDINGS_DIR", os.getcwd()),
                                 self._refresh_all).exec()
        except Exception as exc:
            print(f"[iris] manage speakers failed: {exc}")
    # ---- live wake-word listener ------------------------------------------
    # "Live transcription" here means: periodically peek a short rolling
    # window of the live ring buffer, run it through the EXISTING file-based
    # transcription queue (Controller.transcribe_file), and check the result
    # against iris_query.is_photo_trigger — the same check already gating the
    # typed-chat trigger. This is not literal word-by-word streaming ASR
    # (the underlying Transcriber is file-based, not a streaming model); it's
    # a practical approximation built on what's actually available. Windows
    # overlap (6s window, peeked every 3s) so a phrase near a window boundary
    # isn't split across two snippets and missed.
    # Whisper-small runs ~1.5-2x realtime on this CPU, so a ~6s window takes
    # ~9-12s to transcribe. The listener is sequential (one snippet at a time),
    # paced by transcription latency: peek -> transcribe -> show -> peek next.
    _WAKE_WINDOW_SECONDS = 6.0      # nominal window; actual size is adaptive
    _WAKE_WINDOW_MIN = 5.0
    _WAKE_WINDOW_MAX = 12.0
    _WAKE_CYCLE_MS = 300           # near-immediate next peek (latency paces us)
    _WAKE_COOLDOWN_SECONDS = 8.0
    _WAKE_POLL_MS = 700
    _WAKE_POLL_MAX = 40            # ~28s max wait — comfortably covers ~6-12s
    def set_wake_callback(self, fn) -> None:
        """Called with the heard phrase text when a wake trigger fires.
        Wired by IrisApp once the chat tab exists. No-op (listener still
        works, just doesn't act) if never set."""
        self._wake_callback = fn
    def _on_live_transcribe_clicked(self) -> None:
        if self._wake_active:
            self._stop_live_transcription()
        else:
            self._start_live_transcription()
    def _start_live_transcription(self) -> None:
        if not hasattr(self.controller, "peek_audio_wav"):
            self.dot_wake.set(
                on=False,
                text="Live transcription: unavailable (backend needs the "
                     "peek_audio_wav update)")
            return
        try:
            self._wake_dir = tempfile.mkdtemp(prefix="iris_wake_")
        except Exception:
            self.dot_wake.set(on=False,
                              text="Live transcription: couldn't start "
                                   "(no scratch directory)")
            return

        # Start mic capture FIRST so VU/input level can respond immediately
        # when live transcription begins (avoids the "first click doesn't
        # select a usable input device" behavior).
        self._wake_owns_mic = False
        source = "ESP32 stream"

        # helper: attempt mic once and log outcome
        def _try_mic_once() -> bool:
            if not hasattr(self.controller, "start_mic_capture"):
                return False
            try:
                ok = bool(self.controller.start_mic_capture())
            except Exception as e:
                ok = False
                print(f"[wake] start_mic_capture() exception: {e}")
            print(f"[wake] start_mic_capture() -> {ok}")
            return ok

        if _try_mic_once():
            self._wake_owns_mic = True
            source = "mic"
        else:
            print("[wake] mic unavailable on first attempt; retrying in 1.0s...")
            time.sleep(1.0)
            if _try_mic_once():
                self._wake_owns_mic = True
                source = "mic"
            else:
                print("[wake] mic still unavailable; falling back to ESP32 stream")
                self._set_live_panel(
                    "No microphone input device was available, so live "
                    "transcription is falling back to the ESP32 audio stream. "
                    "If no ESP32 is streaming, nothing will appear.\n")

        # Live session aggregation state
        self._wake_active = True
        self._wake_counter = 0
        self._wake_cooldown_until = 0.0
        self._wake_last_text = None
        self._wake_last_peek_ts = time.time()

        # Save/catenate live audio into a single WAV on stop
        self._wake_session_id = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        self._wake_live_stem = os.path.join(
            self._c("RECORDINGS_DIR", os.getcwd()),
            f"live_{self._wake_session_id}")
        self._wake_copied_snippets: list[str] = []  # wav paths in RECORDINGS_DIR
        self._wake_output_wav = self._wake_live_stem + ".wav"
        self._wake_output_txt = self._wake_live_stem + ".txt"

        # Create a new “Live (together)” tab for this start (new panel/tab per session)
        try:
            new_txt = self._textbox(read_only=True, mono=True)
            new_txt.setFixedHeight(120)
            session_label = f"session {self.live_together_tabs.count()+1}"
            self.live_together_tabs.addTab(new_txt, session_label)
            self.live_together_tabs.setCurrentWidget(new_txt)
            self.txt_live_together = new_txt
            self.txt_live_together.setPlainText("")
        except Exception:
            # Fallback: if tab creation fails, keep things functional by
            # writing to the rolling transcript panel only.
            self.txt_live_together = None

        # Clear panels for this new session
        self.txt_transcript.setPlainText("")
        self.txt_summary.setPlainText(
            "Live transcription is on. Saving snippets and will "
            "concatenate + summarize on stop.")

        self.btn_wake.setText("\U0001F507  Stop Live Transcription")
        self.dot_wake.set(on=True,
                          text=f"Live transcription: listening ({source})\u2026")
        if self._wake_owns_mic:
            self._set_live_panel("")
        self.lbl_transcript_target.setText("(live transcription)")
        QTimer.singleShot(500, self._wake_cycle_peek)
    def _set_live_panel(self, text: str) -> None:
        try:
            self.txt_transcript.setPlainText(text)
        except Exception:
            pass
    def _stop_live_transcription(self) -> None:
        self._wake_active = False
        self.btn_wake.setText("\U0001F399  Start Live Transcription")
        self.dot_wake.set(on=False, text="Live transcription: off")

        if self._wake_owns_mic and hasattr(self.controller, "stop_mic_capture"):
            try:
                self.controller.stop_mic_capture()
            except Exception:
                pass
        self._wake_owns_mic = False

        # Concatenate copied snippets into one WAV and auto-summarize.
        # This uses the copied snippets in RECORDINGS_DIR (so we can safely
        # delete the temporary wake scratch directory).
        combined_ok = False
        try:
            snippets = getattr(self, "_wake_copied_snippets", [])
            if snippets:
                self._concat_live_snippets_to_wav(snippets,
                                                   self._wake_output_wav)
                combined_ok = True

                # sidecar text (the accumulated “together” transcript)
                try:
                    together = (self.txt_live_together.toPlainText().strip()
                                 if self.txt_live_together is not None else "")
                    if together:
                        with open(self._wake_output_txt, "w",
                                  encoding="utf-8") as f:
                            f.write(together + "\n")
                except Exception:
                    pass

                # Auto-summarize the saved combined file
                try:
                    self.txt_summary.setPlainText(
                        "Live transcription stopped. Summarizing saved live audio…")
                    if hasattr(self.controller, "summarize_file"):
                        self.controller.summarize_file(self._wake_output_wav)
                except Exception:
                    pass
        except Exception as e:
            print(f"[wake] concat/summarize failed: {e}")

        # Cleanup scratch snippets + json from peek_audio_wav temp dir.
        # Important: the backend transcriber writes txt/json sidecars next to
        # the wav inside this same temp directory. If we delete the directory
        # immediately on stop, the transcriber thread can crash with
        # FileNotFoundError. So we delete with a delay.
        if self._wake_dir:
            wake_dir = self._wake_dir
            self._wake_dir = None

            def _delayed_cleanup():
                # Give the transcriber thread enough time to finish
                # writing snippet_XXXX.txt/json before removing the wake_dir.
                # Windows PortAudio/mic issues can delay the transcription
                # pipeline, so 10s was not sufficient.
                try:
                    time.sleep(60.0)
                    shutil.rmtree(wake_dir, ignore_errors=True)
                except Exception:
                    pass

            threading.Thread(target=_delayed_cleanup, daemon=True).start()

        # Hand the right panel back to whatever recording was selected
        # (keep summary if we just started auto-summarization).
        try:
            if not combined_ok:
                if self._selected_path:
                    self._show_content(self._selected_path)
                else:
                    self.lbl_transcript_target.setText("(no recording selected)")
        except Exception:
            pass
    def _wake_cycle_peek(self) -> None:
        if not self._wake_active:
            return
        if time.time() < self._wake_cooldown_until:
            QTimer.singleShot(self._WAKE_CYCLE_MS, self._wake_cycle_peek)
            return
        self._wake_counter += 1
        snippet = os.path.join(self._wake_dir,
                                f"snippet_{self._wake_counter:04d}.wav")
        # Adaptive window: grab roughly the audio that accumulated since the
        # last peek (transcription latency means that's >6s), clamped, so we
        # don't drop speech that arrived while the previous chunk transcribed.
        now = time.time()
        window = now - self._wake_last_peek_ts
        window = max(self._WAKE_WINDOW_MIN,
                     min(self._WAKE_WINDOW_MAX, window))
        self._wake_last_peek_ts = now
        try:
            ok = self.controller.peek_audio_wav(window, snippet)
        except Exception:
            ok = False
        if not ok:
            QTimer.singleShot(self._WAKE_CYCLE_MS, self._wake_cycle_peek)
            return
        try:
            if hasattr(self.controller, "transcribe_file_only"):
                self.controller.transcribe_file_only(snippet)
            else:
                self.controller.transcribe_file(snippet)
        except Exception:
            self._cleanup_wake_snippet(snippet)
            QTimer.singleShot(self._WAKE_CYCLE_MS, self._wake_cycle_peek)
            return
        QTimer.singleShot(self._WAKE_POLL_MS,
                          lambda: self._wake_cycle_poll(snippet, 0))
    def _wake_cycle_poll(self, snippet: str, attempts: int) -> None:
        if not self._wake_active:
            self._cleanup_wake_snippet(snippet)
            return
        json_path = os.path.splitext(snippet)[0] + ".json"
        text = self._read_wake_transcript(json_path)
        if text is None and attempts < self._WAKE_POLL_MAX:
            QTimer.singleShot(
                self._WAKE_POLL_MS,
                lambda: self._wake_cycle_poll(snippet, attempts + 1))
            return

        # If we have a snippet wav, copy it into RECORDINGS_DIR so we can
        # concatenate it later on stop. We only copy when we successfully
        # got either some transcript text OR when the json exists (snippet
        # produced). This avoids empty snippets when nothing was buffered.
        try:
            if os.path.exists(snippet):
                # Always copy the audio snippet once it has produced a JSON
                # (regardless of whether text is empty).
                ts = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
                dst = self._wake_live_stem + f"_part_{ts}.wav"
                shutil.copy2(snippet, dst)
                self._wake_copied_snippets.append(dst)
        except Exception as e:
            print(f"[wake] snippet copy failed: {e}")

        # Cleanup only json in temp dir; wav was copied and can be removed.
        self._cleanup_wake_snippet(snippet)

        # Show chunk in rolling transcript
        if text:
            self._append_live_text(text)

        if text and iq is not None and iq.is_photo_trigger(text):
            heard = text.strip()
            short = heard if len(heard) <= 50 else heard[:47] + "\u2026"
            self.dot_wake.set(
                on=True, text=f"Live transcription: heard \u201c{short}\u201d "
                             "\u2014 capturing\u2026")
            self._wake_cooldown_until = (
                time.time() + self._WAKE_COOLDOWN_SECONDS)
            if self._wake_callback is not None:
                try:
                    self._wake_callback(heard)
                except Exception:
                    pass
            QTimer.singleShot(1800, self._reset_wake_status)

        QTimer.singleShot(self._WAKE_CYCLE_MS, self._wake_cycle_peek)
    def _append_live_text(self, text: str) -> None:
        """Append one rolling transcript chunk to the right panel (chunked),
        and also append to the accumulated 'together' transcript."""
        text = (text or "").strip()
        if not text or text == self._wake_last_text:
            return
        self._wake_last_text = text
        try:
            ts = datetime.now().strftime("%H:%M:%S")
            line = f"[{ts}]  {text}"
            cur = self.txt_transcript.toPlainText().rstrip()
            self.txt_transcript.setPlainText((cur + "\n" + line) if cur else line)
            sb = self.txt_transcript.verticalScrollBar()
            sb.setValue(sb.maximum())
        except Exception:
            pass

        # “Together” accumulation: keep adding the new text after the old text.
        # This is intentionally simple: whisper chunks are text continuations,
        # and joining with a space produces "hey jarvis" across chunk boundaries.
        try:
            if self.txt_live_together is None:
                return
            tcur = self.txt_live_together.toPlainText().strip()
            if not tcur:
                self.txt_live_together.setPlainText(text)
            else:
                if not tcur.endswith((" ", "\n")):
                    tcur += " "
                self.txt_live_together.setPlainText(tcur + text)
            sb2 = self.txt_live_together.verticalScrollBar()
            sb2.setValue(sb2.maximum())
        except Exception:
            pass
    def _reset_wake_status(self) -> None:
        if self._wake_active:
            self.dot_wake.set(on=True, text="Live transcription: listening\u2026")
    @staticmethod
    def _read_wake_transcript(json_path: str) -> Optional[str]:
        """None = not ready yet (keep polling). '' = ready, but empty/no
        speech (stop polling, no trigger). Non-empty = ready, has text."""
        if not os.path.exists(json_path):
            return None
        try:
            with open(json_path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            return None
        t = data.get("transcript")
        if isinstance(t, str) and t.strip():
            return t
        segs = data.get("segments")
        if isinstance(segs, list):
            parts = [seg.get("text", "") for seg in segs
                     if isinstance(seg, dict)]
            joined = " ".join(p for p in parts if p).strip()
            if joined:
                return joined
        return ""
    @staticmethod
    def _cleanup_wake_snippet(snippet: str) -> None:
        # snippet wav is in temp dir; safe to remove after we've copied it.
        for p in (snippet, os.path.splitext(snippet)[0] + ".json"):
            try:
                if os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass
    # ---- recordings list ----
    def _refresh_all(self):
        self._refresh_recordings()
        if self.location_tab is not None:
            self.location_tab.refresh()
    def _refresh_recordings(self):
        for btn, _ in self._rows:
            btn.deleteLater()
        self._rows.clear()
        files = sorted(glob.glob(os.path.join(
            self._c("RECORDINGS_DIR", os.getcwd()), "*.wav")), reverse=True)
        for path in files:
            btn = self._make_row(path)
            self._list_lay.insertWidget(self._list_lay.count() - 1, btn)
            self._rows.append((btn, path))
        if self._selected_path and self._selected_path in files:
            self._show_content(self._selected_path)
            self._highlight()
        elif files:
            self._select(files[0])
        else:
            self._show_content(None)
    def _make_row(self, path: str) -> QPushButton:
        base = os.path.splitext(path)[0]
        flags = ""
        if os.path.exists(base + ".txt"):            flags += "\u2713"
        if os.path.exists(base + ".embeddings.npz"): flags += "\U0001F464"
        if os.path.exists(base + ".summary.txt"):    flags += "\U0001F4CB"
        if os.path.exists(base + ".location.json"):  flags += "\U0001F4CD"
        if not flags:                                flags = "\u22EF"
        dur = self._wav_duration(path)
        m, s = divmod(int(dur), 60)
        name = os.path.basename(path)
        parts = name.replace("recording_", "").replace(".wav", "").split("_chunk")
        ts_part = parts[0] if len(parts) == 2 else name
        chunk = f"ch{parts[1]}" if len(parts) == 2 else ""
        label = f"  {ts_part.replace('_', ' ')}  {chunk}  {m:02d}:{s:02d}  {flags}"
        btn = QPushButton(label)
        btn.setCursor(Qt.CursorShape.PointingHandCursor)
        btn.setFixedHeight(32)
        self._style_row(btn, selected=False)
        btn.clicked.connect(lambda _=False, p=path: self._select(p))
        return btn
    def _style_row(self, btn: QPushButton, selected: bool):
        if selected:
            bg = f"rgba({_rgb(ACCENT)},0.14)"
            border = f"rgba({_rgb(ACCENT)},0.30)"
            fg = ACCENT
        else:
            bg = "transparent"
            border = "transparent"
            fg = TEXT_PRIMARY
        btn.setStyleSheet(
            "QPushButton {"
            f"color:{fg}; background:{bg}; border:1px solid {border};"
            "border-radius:8px; text-align:left; padding:0 8px;"
            f"font-family:'{FONT_MONO}','Consolas',monospace; font-size:11px;"
            "}"
            "QPushButton:hover { background: rgba(255,255,255,0.07); }")
    def _highlight(self):
        for btn, path in self._rows:
            self._style_row(btn, selected=(path == self._selected_path))
    def _select(self, path: str):
        self._selected_path = path
        self._show_content(path)
        self._highlight()
        loc = load_location_sidecar(path)
        if loc and self.location_tab is not None:
            self.location_tab.center_on((loc["lat"], loc["lon"]))
    # ---- content display ----
    def _show_content(self, path: Optional[str]):
        self._show_summary(path)
        self._show_transcript(path)
    def _show_summary(self, path: Optional[str]):
        if path is None:
            self.txt_summary.setPlainText("")
            return
        sp = os.path.splitext(path)[0] + ".summary.txt"
        if os.path.exists(sp):
            try:
                with open(sp, "r", encoding="utf-8") as f:
                    self.txt_summary.setPlainText(f.read().strip())
            except Exception:
                self.txt_summary.setPlainText("(error reading summary)")
        else:
            self.txt_summary.setPlainText(
                "No summary yet. Auto-summarize runs after transcription, "
                "or click \u21bb Re-summarize.")
    def _show_transcript(self, path: Optional[str]):
        if path is None:
            self.lbl_transcript_target.setText("(no recording selected)")
            self.txt_transcript.setPlainText("")
            return
        self.lbl_transcript_target.setText(os.path.basename(path))
        jp = os.path.splitext(path)[0] + ".json"
        if not os.path.exists(jp):
            self.txt_transcript.setPlainText(
                "No transcript yet. Click \U0001F4DD to generate one.")
            return
        try:
            with open(jp, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            self.txt_transcript.setPlainText(f"(error reading JSON: {e})")
            return
        out = []
        show_ts = self._c("GUI_SHOW_TIMESTAMPS", False)
        for seg in data.get("segments", []):
            speaker = seg.get("speaker")
            conf = seg.get("speaker_confidence", 0.0)
            kind = seg.get("speaker_kind", "unknown")
            text = seg.get("text", "").strip()
            line = ""
            if show_ts:
                line += (f"[{self._fmt_ts(seg['start'])} \u2192 "
                         f"{self._fmt_ts(seg['end'])}]  ")
            if speaker:
                line += (f"[{speaker} \u2014 {conf:.0%}]  " if kind == "weak"
                         else f"[{speaker}]  ")
            line += text
            out.append(line)
        self.txt_transcript.setPlainText("\n\n".join(out))
    # ---- tag speaker (port of _on_tag_speaker_manual) ----
    def _on_tag_speaker_manual(self):
        if not self._selected_path:
            return
        jp = os.path.splitext(self._selected_path)[0] + ".json"
        if not os.path.exists(jp):
            return
        try:
            with open(jp, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            return
        segments = data.get("segments", [])
        if not segments:
            return
        labels = list(dict.fromkeys(
            seg.get("speaker", "Unknown") for seg in segments
            if seg.get("speaker")))
        if not labels:
            for seg in segments:
                seg["speaker"] = "Speaker 1"
                seg["speaker_kind"] = "unknown"
                seg["speaker_confidence"] = 0.0
            labels = ["Speaker 1"]
        dlg = QDialog(self)
        dlg.setWindowTitle("Tag Speaker")
        dlg.resize(420, 240)
        dlg.setStyleSheet(f"QDialog {{ background:{BG_MID}; }}"
                          f"QLabel {{ color:{TEXT_PRIMARY};"
                          f"font-family:'{FONT_SANS}'; }}")
        v = QVBoxLayout(dlg)
        v.addWidget(QLabel("Who is speaking in this recording?"))
        cap = QLabel("Pick the current label, then enter the real name.")
        cap.setStyleSheet(f"color:{TEXT_MUTED}; font-size:11px;")
        v.addWidget(cap)
        v.addWidget(QLabel("Current label in transcript:"))
        combo = QComboBox()
        combo.addItems(labels)
        combo.setStyleSheet(
            f"QComboBox {{ color:{TEXT_PRIMARY}; background:rgba(255,255,255,0.06);"
            f"border:1px solid {GLASS_BORDER_SOFT}; border-radius:8px;"
            "padding:4px 8px; }")
        v.addWidget(combo)
        v.addWidget(QLabel("Real name (who this actually is):"))
        entry = QLineEdit()
        entry.setPlaceholderText("e.g. Humza, Mom, \u2026")
        entry.setStyleSheet(
            f"QLineEdit {{ color:{TEXT_PRIMARY}; background:rgba(255,255,255,0.06);"
            f"border:1px solid {GLASS_BORDER_SOFT}; border-radius:8px;"
            "padding:6px 8px; }")
        v.addWidget(entry)
        def _save():
            old = combo.currentText()
            new = entry.text().strip()
            if not new:
                return
            for seg in segments:
                if seg.get("speaker") == old:
                    seg["speaker"] = new
                    seg["speaker_kind"] = "strict"
                    seg["speaker_confidence"] = 1.0
            data["diarized"] = True
            try:
                with open(jp, "w", encoding="utf-8") as f:
                    json.dump(data, f, indent=2)
            except Exception as e:
                print(f"[gui] could not save speaker tag: {e}")
                dlg.reject(); return
            db = getattr(self.controller, "speaker_db", None)
            if db is not None:
                try:
                    if new not in db.list_names():
                        import numpy as _np
                        db.create(new, _np.zeros(192, dtype=_np.float32))
                except Exception as e:
                    print(f"[gui] could not create placeholder profile: {e}")
                emb_path = (os.path.splitext(self._selected_path)[0]
                            + ".embeddings.npz")
                if os.path.exists(emb_path):
                    try:
                        import numpy as np
                        npz = np.load(emb_path)
                        cids = list({seg.get("_cluster", -1) for seg in segments
                                     if seg.get("speaker") == new
                                     and seg.get("_cluster", -1) >= 0})
                        for cid in cids:
                            key = f"cluster_{cid}"
                            if key in npz:
                                db.add_to(new, npz[key])
                    except Exception as e:
                        print(f"[gui] could not save voiceprint: {e}")
            dlg.accept()
            self._show_content(self._selected_path)
            self._refresh_recordings()
        entry.returnPressed.connect(_save)
        row = QHBoxLayout()
        row.addWidget(_audio_btn("Save", _save, accent=_rgb(COLOR_STATUS_ON),
                                 fg="#86efac", width=90))
        row.addWidget(_audio_btn("Cancel", dlg.reject, width=90))
        row.addStretch(1)
        v.addLayout(row)
        dlg.exec()
    @staticmethod
    def _fmt_ts(s: float) -> str:
        m = int(s // 60); sec = s - m * 60
        return f"{m:02d}:{sec:05.2f}"
    @staticmethod
    def _wav_duration(path: str) -> float:
        try:
            with wave.open(path, "rb") as wf:
                return wf.getnframes() / wf.getframerate()
        except Exception:
            return 0.0
# ─────────────────────────────────────────────────────────────────────────────
# Location tab — the map (Leaflet in QWebEngineView, else a located-recordings
# list). Driven by the audio tab: location events + recording selection.
# ─────────────────────────────────────────────────────────────────────────────
class LocationTab(QWidget):
    def __init__(self, parent, app_config):
        super().__init__(parent)
        self.cfg = app_config
        self._map_view = None
        self._map_note = None
        if app_config is None:
            self._build_notice()
            return
        self._build()
        self.refresh()
    def _c(self, attr, default):
        return getattr(self.cfg, attr, default) if self.cfg else default
    def _build_notice(self):
        outer = QVBoxLayout(self)
        outer.addStretch(1)
        card = GlassFrame(self, radius=18, blur=30, dy=8)
        card.setMaximumWidth(520)
        cl = QVBoxLayout(card)
        cl.setContentsMargins(28, 24, 28, 26)
        t = QLabel("location & gps")
        t.setStyleSheet(f"color:{TEXT_PRIMARY}; background:transparent;"
                        f"border:none; font-family:'{FONT_SANS}';"
                        "font-size:18px; font-weight:700;")
        note = QLabel("Location backend isn't loaded. Run iris_gui.py from the "
                      "project folder so recordings and their location "
                      "sidecars are available, and the map appears here.")
        note.setWordWrap(True)
        note.setStyleSheet(f"color:{TEXT_MUTED}; background:transparent;"
                           f"border:none; font-family:'{FONT_SANS}';"
                           "font-size:12px;")
        cl.addWidget(t)
        cl.addWidget(note)
        wrap = QHBoxLayout()
        wrap.addStretch(1); wrap.addWidget(card); wrap.addStretch(1)
        outer.addLayout(wrap)
        outer.addStretch(2)
    def _build(self):
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        frame = GlassFrame(self, radius=16, blur=24, dy=6, shadow_alpha=120,
                           top="rgba(255,255,255,0.06)",
                           mid="rgba(255,255,255,0.035)",
                           bot="rgba(255,255,255,0.02)",
                           border=GLASS_BORDER_SOFT)
        outer.addWidget(frame)
        lay = QVBoxLayout(frame)
        lay.setContentsMargins(14, 12, 14, 12)
        lay.setSpacing(6)
        head = QHBoxLayout()
        title = QLabel("location & gps")
        title.setStyleSheet(f"color:{TEXT_PRIMARY}; background:transparent;"
                            f"border:none; font-family:'{FONT_SANS}';"
                            "font-size:15px; font-weight:700;")
        head.addWidget(title)
        head.addStretch(1)
        self.lbl_location = QLabel("")
        self.lbl_location.setStyleSheet(
            f"color:{TEXT_DIM}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:11px;")
        head.addWidget(self.lbl_location)
        lay.addLayout(head)
        if QWebEngineView is not None:
            try:
                self._map_view = QWebEngineView()
                self._map_view.setStyleSheet("border-radius:10px;")
                lay.addWidget(self._map_view, 1)
            except Exception:
                self._map_view = None
        if self._map_view is None:
            self._map_note = QTextEdit()
            self._map_note.setReadOnly(True)
            self._map_note.setStyleSheet(
                "QTextEdit {"
                f"color:{TEXT_PRIMARY}; background: rgba(255,255,255,0.04);"
                f"border: 1px solid {GLASS_BORDER_SOFT}; border-radius: 10px;"
                f"padding: 10px; font-family:'{FONT_MONO}','Consolas',monospace;"
                "font-size:12px; }")
            self._map_note.setPlainText(
                "Map needs PyQt6-WebEngine.\n"
                "  pip install PyQt6-WebEngine\n\n"
                "Located recordings will be listed here until it's installed.")
            lay.addWidget(self._map_note, 1)
    # ---- public API used by the audio tab ----
    def set_location(self, loc: dict):
        if self.cfg is None:
            return
        try:
            self.lbl_location.setText(f"{loc['city']}, {loc['region']}")
            self.center_on((loc["lat"], loc["lon"]))
        except Exception:
            pass
    def center_on(self, latlon):
        if self.cfg is not None:
            self._render(center=latlon)
    def refresh(self):
        if self.cfg is not None:
            self._render()
    # ---- render ----
    def _render(self, center=None):
        files = sorted(glob.glob(os.path.join(
            self._c("RECORDINGS_DIR", os.getcwd()), "*.wav")))
        located = []
        for path in files:
            loc = load_location_sidecar(path)
            if loc:
                located.append((loc["lat"], loc["lon"], path))
        if self._map_view is None:
            if self._map_note is not None:
                if located:
                    lines = ["Located recordings:\n"]
                    for lat, lon, p in located:
                        lines.append(f"  \u2022 {os.path.basename(p)}  "
                                     f"({lat:.4f}, {lon:.4f})")
                    self._map_note.setPlainText("\n".join(lines))
                else:
                    self._map_note.setPlainText("No located recordings yet.")
            return
        if center is None:
            center = ((located[0][0], located[0][1]) if located
                      else (self._c("MAP_FALLBACK_LAT", 0.0),
                            self._c("MAP_FALLBACK_LON", 0.0)))
        self._map_view.setHtml(self._map_html(located, center))
    def _map_html(self, located, center) -> str:
        tile = self._c("MAP_TILE_URL",
                       "https://tile.openstreetmap.org/{z}/{x}/{y}.png")
        zoom = int(self._c("MAP_DEFAULT_ZOOM", 13))
        clusters = self._cluster_pins(
            located, self._c("MAP_CLUSTER_RADIUS_M", 60))
        markers = []
        for cl in clusters:
            lat = sum(c[0] for c in cl) / len(cl)
            lon = sum(c[1] for c in cl) / len(cl)
            if len(cl) > 1:
                text = f"{len(cl)} recordings"
            else:
                text = (os.path.basename(cl[0][2]).split("_chunk")[0]
                        .replace("recording_", ""))
            markers.append(f"L.marker([{lat},{lon}]).addTo(map)"
                           f".bindPopup({json.dumps(text)});")
        return (
            "<!DOCTYPE html><html><head><meta charset='utf-8'>"
            "<link rel='stylesheet' href='https://unpkg.com/leaflet@1.9.4/dist/leaflet.css'/>"
            "<script src='https://unpkg.com/leaflet@1.9.4/dist/leaflet.js'></script>"
            "<style>html,body,#m{height:100%;margin:0;background:#0b1120;}</style>"
            "</head><body><div id='m'></div><script>"
            f"var map=L.map('m').setView([{center[0]},{center[1]}],{zoom});"
            f"L.tileLayer({json.dumps(tile)},{{maxZoom:19}}).addTo(map);"
            + "".join(markers) +
            "</script></body></html>")
    @staticmethod
    def _cluster_pins(points, radius_m):
        unassigned = list(points)
        clusters = []
        while unassigned:
            seed = unassigned.pop(0)
            cluster = [seed]
            remaining = []
            for p in unassigned:
                if any(LocationTab._hav_m(p[0], p[1], q[0], q[1]) <= radius_m
                       for q in cluster):
                    cluster.append(p)
                else:
                    remaining.append(p)
            unassigned = remaining
            clusters.append(cluster)
        return clusters
    @staticmethod
    def _hav_m(lat1, lon1, lat2, lon2):
        R = 6_371_000.0
        p1, p2 = math.radians(lat1), math.radians(lat2)
        dp = math.radians(lat2 - lat1)
        dl = math.radians(lon2 - lon1)
        a = (math.sin(dp / 2) ** 2
             + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2)
        return 2 * R * math.asin(math.sqrt(a))
# ─────────────────────────────────────────────────────────────────────────────
# Photos tab — gallery of everything captured via "hey iris, take a photo" or
# the manual camera button. Backed by iris_photos.PhotoStore, the same module
# ChatTab uses, both pointed at the same <recordings root>/photos folder.
# ─────────────────────────────────────────────────────────────────────────────
class PhotosTab(QWidget):
    THUMB = 150
    COLS = 5
    def __init__(self, parent, app_config, on_select=None):
        super().__init__(parent)
        self.cfg = app_config
        self._on_select = on_select
        self._store = iphotos.PhotoStore(_photos_dir()) if iphotos is not None else None
        self._build()
        self.refresh()
    def _build(self) -> None:
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        frame = GlassFrame(self, radius=16, blur=24, dy=6, shadow_alpha=120,
                           top="rgba(255,255,255,0.06)",
                           mid="rgba(255,255,255,0.035)",
                           bot="rgba(255,255,255,0.02)",
                           border=GLASS_BORDER_SOFT)
        outer.addWidget(frame)
        lay = QVBoxLayout(frame)
        lay.setContentsMargins(14, 12, 14, 12)
        lay.setSpacing(8)
        head = QHBoxLayout()
        title = QLabel("photos")
        title.setStyleSheet(f"color:{TEXT_PRIMARY}; background:transparent;"
                            f"border:none; font-family:'{FONT_SANS}';"
                            "font-size:15px; font-weight:700;")
        head.addWidget(title)
        self.lbl_count = QLabel("")
        self.lbl_count.setStyleSheet(
            f"color:{TEXT_DIM}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:11px; padding-left:8px;")
        head.addWidget(self.lbl_count)
        head.addStretch(1)
        head.addWidget(_audio_btn("\u21bb Refresh", self.refresh, height=30,
                                  accent=_rgb(ACCENT), fg=ACCENT))
        head.addWidget(_audio_btn("\U0001F4C2 Open folder", self._open_folder,
                                  height=30))
        lay.addLayout(head)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setStyleSheet(
            "QScrollArea{background:transparent;border:none;}"
            "QScrollBar:vertical{width:8px;background:transparent;}"
            "QScrollBar::handle:vertical{background:rgba(255,255,255,0.14);"
            "border-radius:4px;}")
        self._grid_holder = QWidget()
        self._grid_holder.setStyleSheet("background: transparent;")
        self._grid = QGridLayout(self._grid_holder)
        self._grid.setContentsMargins(2, 2, 2, 2)
        self._grid.setHorizontalSpacing(10)
        self._grid.setVerticalSpacing(10)
        scroll.setWidget(self._grid_holder)
        lay.addWidget(scroll, 1)
        self._empty_note = QLabel(
            "No photos yet. Say \u201chey iris, take a photo\u201d in the "
            "Chat tab, or use the \U0001F4F7 button there.")
        self._empty_note.setWordWrap(True)
        self._empty_note.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._empty_note.setStyleSheet(
            f"color:{TEXT_MUTED}; background:transparent; border:none;"
            f"font-family:'{FONT_SANS}'; font-size:12px; padding: 30px;")
        lay.addWidget(self._empty_note)
    def _clear_grid(self) -> None:
        while self._grid.count():
            item = self._grid.takeAt(0)
            w = item.widget()
            if w:
                w.deleteLater()
    def refresh(self) -> None:
        if self._store is None:
            self.lbl_count.setText("(iris_photos.py missing)")
            return
        self._clear_grid()
        photos = self._store.list_all()         # already newest-first
        self.lbl_count.setText(
            f"{len(photos)} photo{'s' if len(photos) != 1 else ''}")
        self._empty_note.setVisible(not photos)
        cols = self.COLS
        for i, p in enumerate(photos):
            tag = _photo_source_label(p.source)
            caption = f"{p.when()}\n{tag}"
            on_click = ((lambda ph=p: self._on_select(ph))
                       if self._on_select is not None else None)
            thumb = PhotoThumb(self._grid_holder, p.path, caption,
                               size=self.THUMB, on_click=on_click)
            self._grid.addWidget(thumb, i // cols, i % cols,
                                 Qt.AlignmentFlag.AlignLeft
                                 | Qt.AlignmentFlag.AlignTop)
    def _open_folder(self) -> None:
        if self._store is None:
            return
        try:
            os.startfile(self._store.dir)              # type: ignore
        except Exception:
            try:
                subprocess.Popen(["xdg-open", self._store.dir])
            except Exception:
                pass
    def showEvent(self, event) -> None:
        self.refresh()
        super().showEvent(event)
# ─────────────────────────────────────────────────────────────────────────────
# Top tab bar — glass segmented buttons (chat / audio / location / people / stream)
# ─────────────────────────────────────────────────────────────────────────────
class TabBar(QWidget):
    changed = pyqtSignal(int)
    def __init__(self, parent, labels: list[str]):
        super().__init__(parent)
        self._buttons: list[QPushButton] = []
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 14, 0, 6)
        lay.setSpacing(6)
        lay.addStretch(1)
        for i, name in enumerate(labels):
            b = QPushButton(name)
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.clicked.connect(lambda _=False, idx=i: self._select(idx))
            self._buttons.append(b)
            lay.addWidget(b)
        lay.addStretch(1)
        self._select(0)
    def _select(self, idx: int) -> None:
        for i, b in enumerate(self._buttons):
            on = (i == idx)
            b.setChecked(on)
            if on:
                b.setStyleSheet(
                    "QPushButton {"
                    f"color:{ACCENT};"
                    f"background: rgba({_rgb(ACCENT)},0.14);"
                    f"border: 1px solid rgba({_rgb(ACCENT)},0.30);"
                    "border-radius: 13px; padding: 6px 18px;"
                    f"font-family:'{FONT_MONO}','Consolas',monospace; font-size:13px;"
                    "}")
            else:
                b.setStyleSheet(
                    "QPushButton {"
                    f"color:{TEXT_MUTED};"
                    "background: transparent; border: 1px solid transparent;"
                    "border-radius: 13px; padding: 6px 18px;"
                    f"font-family:'{FONT_MONO}','Consolas',monospace; font-size:13px;"
                    "}"
                    "QPushButton:hover { background: rgba(255,255,255,0.06); }")
        self.changed.emit(idx)
# ─────────────────────────────────────────────────────────────────────────────
# Title strip — macOS-style traffic-light controls + live session timer.
# The whole strip is the window's drag handle (frameless windows have none).
# ─────────────────────────────────────────────────────────────────────────────
class TitleBar(QWidget):
    def __init__(self, parent):
        super().__init__(parent)
        self.setFixedHeight(44)
        self._drag: Optional[QPoint] = None
        self._secs = 0
        lay = QHBoxLayout(self)
        lay.setContentsMargins(18, 0, 20, 0)
        lay.setSpacing(8)
        # Traffic lights — functional: close / minimise / maximise
        lay.addWidget(self._dot("#ff5f57", self._close))   # red
        lay.addWidget(self._dot("#febc2e", self._minimise)) # yellow
        lay.addWidget(self._dot("#28c840", self._maximise)) # green
        lay.addStretch(1)
        self.session = QLabel("iris \u00b7 session 00:00:00")
        self.session.setStyleSheet(
            f"color:{TEXT_DIM}; background:transparent; border:none;"
            f"font-family:'{FONT_MONO}','Consolas',monospace; font-size:12px;")
        lay.addWidget(self.session)
        self._timer = QTimer(self)
        self._timer.timeout.connect(self._tick)
        self._timer.start(1000)
    def _dot(self, color: str, on_click) -> QPushButton:
        b = QPushButton()
        b.setCursor(Qt.CursorShape.PointingHandCursor)
        b.setFixedSize(13, 13)
        b.setStyleSheet(
            "QPushButton {"
            f"background:{color}; border:none; border-radius:6px;"
            "}"
            "QPushButton:hover { border: 1px solid rgba(0,0,0,0.25); }")
        b.clicked.connect(on_click)
        return b
    def _tick(self) -> None:
        self._secs += 1
        h, rem = divmod(self._secs, 3600)
        m, s = divmod(rem, 60)
        self.session.setText(f"iris \u00b7 session {h:02d}:{m:02d}:{s:02d}")
    def _close(self):     self.window().close()
    def _minimise(self):  self.window().showMinimized()
    def _maximise(self):
        w = self.window()
        w.showNormal() if w.isMaximized() else w.showMaximized()
    # Drag the frameless window by its title strip
    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._drag = (e.globalPosition().toPoint()
                          - self.window().frameGeometry().topLeft())
            e.accept()
    def mouseMoveEvent(self, e):
        if self._drag is not None and (e.buttons() & Qt.MouseButton.LeftButton):
            self.window().move(e.globalPosition().toPoint() - self._drag)
            e.accept()
    def mouseReleaseEvent(self, e):
        self._drag = None
    def mouseDoubleClickEvent(self, e):
        self._maximise()
# ─────────────────────────────────────────────────────────────────────────────
# Main IRIS window — a single rounded, frameless "bubble" floating on the desktop
# ─────────────────────────────────────────────────────────────────────────────
class IrisApp(QWidget):
    TAB_NAMES = ["chat", "audio", "location", "people", "stream", "photos"]
    def __init__(self, controller=None):
        super().__init__()
        self.controller = controller
        self.setWindowTitle("iris")
        self.resize(1400, 850)
        self.setMinimumSize(1100, 700)
        # Frameless + translucent so the rounded corners show the desktop behind
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint
                            | Qt.WindowType.Window)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        root = QVBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)
        self.titlebar = TitleBar(self)
        root.addWidget(self.titlebar)
        self.tabbar = TabBar(self, self.TAB_NAMES)
        root.addWidget(self.tabbar)
        # Body holds the tab stack inside a small gutter so panels float and the
        # rounded window corners stay clean (no square widget pokes through).
        body = QWidget(self)
        body.setStyleSheet("background: transparent;")
        bl = QVBoxLayout(body)
        bl.setContentsMargins(14, 0, 14, 14)
        bl.setSpacing(0)
        self.stack = QStackedWidget(body)
        bl.addWidget(self.stack)
        root.addWidget(body, 1)
        # Location tab built first so the audio tab can drive its map.
        self.location = LocationTab(self, config)
        # Audio tab built next so the chat can drive it for auto-transcription.
        self.audio = AudioTab(self, controller, config,
                              location_tab=self.location,
                              switch=lambda: self.tabbar._select(1))
        # Chat first in the stack; it can switch to the audio tab + drive it.
        self.chat = ChatTab(
            self, controller=controller, audio_gui=self.audio,
            switch_to_audio=lambda: self.tabbar._select(1))
        def _on_wake_trigger(phrase):
            self.chat.handle_voice_trigger(phrase)
            self.tabbar._select(0)
        self.audio.set_wake_callback(_on_wake_trigger)
        self.stack.addWidget(self.chat)
        self.stack.addWidget(self.audio)
        self.stack.addWidget(self.location)
        self.stack.addWidget(PlaceholderTab(
            self, "people registry",
            ["face enrollment from camera",
             "DeepFace recognition \u00b7 SQLite registry",
             "live detection feed", "speaker-to-face matching"], "M5"))
        self.stack.addWidget(PlaceholderTab(
            self, "stream monitor",
            ["live audio waveform", "word-by-word transcription",
             "speaker diarization timeline", "wake word confidence"], "M2"))
        def _select_photo_from_gallery(photo):
            self.chat.select_photo(photo)
            self.tabbar._select(0)
        self.photos = PhotosTab(self, config, on_select=_select_photo_from_gallery)
        self.stack.addWidget(self.photos)
        self.tabbar.changed.connect(self.stack.setCurrentIndex)
        self.stack.setCurrentIndex(0)
        # Bottom-right resize grip (frameless windows lose native resizing)
        self._grip = QSizeGrip(self)
        self._grip.setFixedSize(18, 18)
        self._grip.setStyleSheet("background: transparent;")
    # Paint the rounded gradient shell + a thin outline = the "bubble"
    def paintEvent(self, _evt):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        rect = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        path = QPainterPath()
        path.addRoundedRect(rect, WINDOW_RADIUS, WINDOW_RADIUS)
        g = QLinearGradient(0, 0, self.width(), self.height())
        g.setColorAt(0.0, QColor(BG_TOP))
        g.setColorAt(0.55, QColor(BG_MID))
        g.setColorAt(1.0, QColor(BG_BOT))
        p.fillPath(path, QBrush(g))
        pen = QPen(WINDOW_OUTLINE)
        pen.setWidth(1)
        p.setPen(pen)
        p.drawPath(path)
    def resizeEvent(self, evt):
        self._grip.move(self.width() - self._grip.width() - 8,
                        self.height() - self._grip.height() - 8)
        super().resizeEvent(evt)
    def closeEvent(self, evt):
        try:
            if self.controller is not None:
                self.controller.shutdown()
        except Exception:
            pass
        super().closeEvent(evt)
def main() -> int:
    app = QApplication(sys.argv)
    # Prefer Cascadia Code; fall back to a mono the OS has.
    families = set(QFontDatabase.families())
    mono = ("Cascadia Code" if "Cascadia Code" in families else
            "Consolas" if "Consolas" in families else "Monospace")
    globals()["FONT_MONO"] = mono
    app.setFont(QFont(FONT_SANS if FONT_SANS in families else "Sans", 10))
    controller = None
    if Controller is not None:
        try:
            controller = Controller()
            if hasattr(controller, "start"):
                controller.start()
        except Exception as exc:
            print(f"[iris] backend controller unavailable: {exc}")
            controller = None
    win = IrisApp(controller)
    win.show()
    try:
        return app.exec()
    finally:
        try:
            if controller is not None:
                controller.shutdown()
        except Exception:
            pass
if __name__ == "__main__":
    sys.exit(main())
