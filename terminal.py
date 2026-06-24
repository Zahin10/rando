"""
ESP32 Combined Receiver — Video + Photo (no YOLO, single player)
"""

import os
import queue
import re
import socket
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox
from datetime import datetime

try:
    import cv2
    HAVE_CV2 = True
except ImportError:
    HAVE_CV2 = False

# ===== Settings =====
SAVE_FOLDER        = r"C:\Users\delete me\Desktop\ESP32_Recording"
PHOTO_FOLDER       = r"C:\Users\delete me\Desktop\camera_photos"
TRANSFER_PORT      = 5010
CMD_PORT           = 5005
PHOTO_CMD_PORT     = 5006
PHOTO_RECEIVE_PORT = 5011
PAUSE_CMD_PORT     = 5007
COMPUTER_IP        = "0.0.0.0"
ESP32_IP           = "192.168.1.210"

VID_W = 480
VID_H = 320

TIMESTAMP_RE = re.compile(r"_(\d{8}_\d{6})")

BG       = "#1e1e1e"
PANEL_BG = "#252526"
CARD_BG  = "#2d2d30"
FG       = "#d4d4d4"
MUTED    = "#9a9a9a"
ACCENT   = "#3b82f6"
GREEN    = "#22c55e"
RED      = "#ef4444"
ORANGE   = "#f59e0b"
CYAN     = "#06b6d4"
YELLOW   = "#eab308"
FONT     = ("Segoe UI", 10)
MONO     = ("Consolas", 9)


class ReceiverApp:
    def __init__(self, root):
        self.root = root
        root.title("ESP32 Video + Photo Receiver")
        root.geometry("1000x780")
        root.configure(bg=BG)

        self.clip_queue          = queue.Queue()
        self.clips               = {}
        self.server_socket       = None
        self.photo_server_socket = None
        self.listening           = False
        self.stop_event          = threading.Event()
        self.pending_iid         = None
        self.esp32_ip            = ESP32_IP
        self.paused              = False   # pause state

        # Video player state
        self.cap             = None
        self.playing         = False
        self.after_id        = None
        self.current_frame   = 0
        self.frame_count     = 0
        self.fps             = 15
        self.delay_ms        = 66
        self.updating_slider = False
        self.current_path    = None

        self._build_style()
        self._build_layout()
        self._load_existing_recordings()
        self._log("Ready. Click Start Listening to wait for the ESP32.")

        self.root.after(300, self._poll_queue)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _build_style(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview",
            background=CARD_BG, fieldbackground=CARD_BG,
            foreground=FG, rowheight=24, font=MONO, borderwidth=0)
        style.configure("Treeview.Heading",
            background=PANEL_BG, foreground=MUTED, font=FONT, borderwidth=0)
        style.map("Treeview", background=[("selected", ACCENT)])

    def _build_layout(self):
        sidebar = tk.Frame(self.root, bg=PANEL_BG, width=280)
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)
        main = tk.Frame(self.root, bg=BG)
        main.pack(side="left", fill="both", expand=True)
        self._build_status_panel(sidebar)
        self._build_main_panel(main)

    def _build_status_panel(self, parent):
        tk.Label(parent, text="Status", bg=PANEL_BG, fg=FG,
                 font=("Segoe UI", 12, "bold")).pack(anchor="w", padx=16, pady=(16, 8))

        self.conn_dot,  self.conn_label  = self._status_row(parent, "ESP32: waiting...")
        self.srv_dot,   self.srv_label   = self._status_row(parent, "Receiver: stopped")
        self.photo_dot, self.photo_label = self._status_row(parent, "Photo: idle")
        self.pause_dot, self.pause_label = self._status_row(parent, "Recording: running")

        log_frame = tk.Frame(parent, bg=PANEL_BG)
        log_frame.pack(fill="both", expand=True, padx=16, pady=(8, 8))
        self.log_box = tk.Text(log_frame, bg=CARD_BG, fg=FG, font=MONO,
                               height=10, wrap="word", borderwidth=0,
                               highlightthickness=0, state="disabled")
        self.log_box.pack(fill="both", expand=True)

        # Pending clip controls
        self.pending_frame = tk.Frame(parent, bg=PANEL_BG)
        self.pending_frame.pack(fill="x")
        self.pending_label = tk.Label(self.pending_frame,
            text="No clip waiting on a decision.",
            bg=PANEL_BG, fg=MUTED, font=FONT, wraplength=240, justify="left")
        self.pending_label.pack(anchor="w", padx=16, pady=(8, 4))

        btn_row = tk.Frame(self.pending_frame, bg=PANEL_BG)
        btn_row.pack(anchor="w", padx=16, pady=(0, 4))

        self.keep_btn = tk.Button(btn_row, text="Keep",
            command=self._keep_pending, bg=GREEN, fg="white",
            relief="flat", padx=10, state="disabled")
        self.keep_btn.pack(side="left", padx=(0, 6))

        self.delete_btn = tk.Button(btn_row, text="Delete",
            command=self._delete_pending, bg=RED, fg="white",
            relief="flat", padx=10, state="disabled")
        self.delete_btn.pack(side="left", padx=(0, 6))

        self.format_btn = tk.Button(btn_row, text="Format SD",
            command=self._format_sd_pending, bg=ORANGE, fg="white",
            relief="flat", padx=10, state="disabled")
        self.format_btn.pack(side="left")

        self.photo_btn = tk.Button(parent, text="📷  Take Photo",
            command=self._request_photo,
            bg=CYAN, fg="white", relief="flat",
            font=("Segoe UI", 11, "bold"), pady=8, state="disabled")
        self.photo_btn.pack(fill="x", padx=16, pady=(8, 4))

        self.pause_btn = tk.Button(parent, text="⏸  Pause Recording",
            command=self._toggle_pause,
            bg=YELLOW, fg="white", relief="flat",
            font=("Segoe UI", 11, "bold"), pady=8, state="disabled")
        self.pause_btn.pack(fill="x", padx=16, pady=(0, 4))

        self.toggle_btn = tk.Button(parent, text="▶  Start Listening",
            command=self._toggle_listening,
            bg=ACCENT, fg="white", relief="flat",
            font=("Segoe UI", 11, "bold"), pady=10)
        self.toggle_btn.pack(fill="x", padx=16, pady=(4, 16))

    def _status_row(self, parent, text):
        row = tk.Frame(parent, bg=PANEL_BG)
        row.pack(anchor="w", padx=16, pady=2)
        dot   = tk.Label(row, text="●", bg=PANEL_BG, fg=MUTED, font=FONT)
        dot.pack(side="left")
        label = tk.Label(row, text=" " + text, bg=PANEL_BG, fg=FG, font=FONT)
        label.pack(side="left")
        return dot, label

    def _build_main_panel(self, parent):
        header = tk.Frame(parent, bg=BG)
        header.pack(fill="x", padx=16, pady=(16, 8))
        tk.Label(header, text="Recordings", bg=BG, fg=FG,
                 font=("Segoe UI", 12, "bold")).pack(side="left")
        toolbar = tk.Frame(header, bg=BG)
        toolbar.pack(side="right")
        tk.Button(toolbar, text="▶  Play",
                  command=self._play_selected,
                  bg=CARD_BG, fg=FG, relief="flat", padx=10).pack(side="left", padx=4)
        tk.Button(toolbar, text="⏹  Stop",
                  command=self._stop_playback,
                  bg=CARD_BG, fg=FG, relief="flat", padx=10).pack(side="left", padx=4)
        tk.Button(toolbar, text="Open Folder",
                  command=self._open_selected_folder,
                  bg=CARD_BG, fg=FG, relief="flat", padx=10).pack(side="left", padx=4)

        player_frame = tk.Frame(parent, bg=BG)
        player_frame.pack(padx=16, pady=(0, 8))

        self.video_title = tk.Label(player_frame, text="No clip loaded",
                                    bg=BG, fg=MUTED, font=FONT)
        self.video_title.pack(pady=(0, 4))

        self.video_label = tk.Label(player_frame, bg="black", borderwidth=0)
        self.video_label.pack()

        blank = self._make_photo(VID_W, VID_H, bytes(VID_W * VID_H * 3))
        self.video_label.config(image=blank)
        self.video_label.image = blank
        self._blank = blank

        controls = tk.Frame(player_frame, bg=BG)
        controls.pack(fill="x", pady=(4, 0))

        self.play_btn = tk.Button(controls, text="▶", width=3,
                                  command=self._toggle_play,
                                  bg=CARD_BG, fg=FG, relief="flat")
        self.play_btn.pack(side="left")

        self.time_label = tk.Label(controls, text="0:00 / 0:00",
                                   bg=BG, fg=MUTED, font=MONO)
        self.time_label.pack(side="right")

        self.scale_var = tk.DoubleVar(value=0)
        self.scale = ttk.Scale(player_frame, from_=0, to=1,
                               orient="horizontal", variable=self.scale_var,
                               command=self._on_seek)
        self.scale.pack(fill="x", pady=(4, 0))

        columns = ("time", "filename", "size", "transfer", "status")
        self.tree = ttk.Treeview(parent, columns=columns, show="headings", height=7)
        for col, label, width in [
            ("time", "Time", 130), ("filename", "Filename", 220),
            ("size", "Size", 75),  ("transfer", "Transfer", 120), ("status", "Status", 100)
        ]:
            self.tree.heading(col, text=label)
            self.tree.column(col, width=width, anchor="w")
        self.tree.pack(fill="both", expand=True, padx=16, pady=(8, 16))
        self.tree.bind("<Double-1>", lambda e: self._play_selected())

    # ── Helpers ───────────────────────────────────────────────────────────────
    def _log(self, msg):
        ts = datetime.now().strftime("%H:%M:%S")
        self.log_box.configure(state="normal")
        self.log_box.insert("end", f"[{ts}] {msg}\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")

    def _make_photo(self, w, h, rgb_bytes):
        header = f"P6\n{w} {h}\n255\n".encode("ascii")
        return tk.PhotoImage(data=header + rgb_bytes)

    def _fmt_time(self, seconds):
        seconds = max(0, int(seconds))
        m, s = divmod(seconds, 60)
        return f"{m}:{s:02d}"

    def _guess_received_at(self, filepath):
        match = TIMESTAMP_RE.search(os.path.basename(filepath))
        if match:
            try:
                return datetime.strptime(match.group(1), "%Y%m%d_%H%M%S")
            except ValueError:
                pass
        return datetime.fromtimestamp(os.path.getmtime(filepath))

    def _load_existing_recordings(self):
        if not os.path.isdir(SAVE_FOLDER):
            return
        entries = []
        for fname in os.listdir(SAVE_FOLDER):
            if not fname.lower().endswith(".avi"):
                continue
            path = os.path.join(SAVE_FOLDER, fname)
            try:
                size = os.path.getsize(path)
            except OSError:
                continue
            entries.append((self._guess_received_at(path), fname, path, size))
        entries.sort(key=lambda e: e[0])
        for received_at, filename, filepath, size in entries:
            size_mb  = size / (1024 * 1024)
            time_str = received_at.strftime("%Y-%m-%d %H:%M:%S")
            iid = self.tree.insert("", "end",
                values=(time_str, filename, f"{size_mb:.2f} MB", "—", "saved"))
            self.clips[iid] = {
                "filename": filename, "filepath": filepath,
                "size_bytes": size, "received_at": received_at,
                "ip": None,
            }
        if entries:
            self._log(f"Loaded {len(entries)} previous recording(s) from disk.")

    # ── Server ────────────────────────────────────────────────────────────────
    def _toggle_listening(self):
        if self.listening:
            self._stop_listening()
        else:
            self._start_listening()

    def _start_listening(self):
        os.makedirs(SAVE_FOLDER, exist_ok=True)
        os.makedirs(PHOTO_FOLDER, exist_ok=True)
        self.stop_event.clear()
        self.listening = True
        self.toggle_btn.config(text="■  Stop Listening", bg=RED)
        self.srv_dot.config(fg=GREEN)
        self.srv_label.config(text=f" Receiver: listening on port {TRANSFER_PORT}")
        self.photo_btn.config(state="normal")
        self.pause_btn.config(state="normal")
        self._log(f"Listening for clips on port {TRANSFER_PORT}...")
        self._log(f"Listening for photos on port {PHOTO_RECEIVE_PORT}...")
        threading.Thread(target=self._server_loop,       daemon=True).start()
        threading.Thread(target=self._photo_server_loop, daemon=True).start()

    def _stop_listening(self):
        self.stop_event.set()
        self.listening = False
        self.toggle_btn.config(text="▶  Start Listening", bg=ACCENT)
        self.srv_dot.config(fg=MUTED)
        self.srv_label.config(text=" Receiver: stopped")
        self.photo_btn.config(state="disabled")
        self.pause_btn.config(state="disabled",
                              text="⏸  Pause Recording", bg=YELLOW)
        self.paused = False
        self.pause_dot.config(fg=MUTED)
        self.pause_label.config(text=" Recording: stopped")
        self._log("Stopped listening.")
        for sock in (self.server_socket, self.photo_server_socket):
            if sock:
                try:
                    sock.close()
                except OSError:
                    pass

    def _server_loop(self):
        server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        server.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 65536)
        server.settimeout(1.0)
        try:
            server.bind((COMPUTER_IP, TRANSFER_PORT))
            server.listen(1)
        except OSError as e:
            self.clip_queue.put({"type": "error",
                                 "message": f"Couldn't bind port {TRANSFER_PORT}: {e}"})
            return
        self.server_socket = server
        while not self.stop_event.is_set():
            try:
                conn, addr = server.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            self.esp32_ip = addr[0]
            self.clip_queue.put({"type": "connect", "ip": addr[0]})
            threading.Thread(target=self._receive_file,
                             args=(conn, addr), daemon=True).start()
        try:
            server.close()
        except OSError:
            pass

    def _photo_server_loop(self):
        server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        server.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 65536)
        server.settimeout(1.0)
        try:
            server.bind((COMPUTER_IP, PHOTO_RECEIVE_PORT))
            server.listen(1)
        except OSError as e:
            self.clip_queue.put({"type": "error",
                                 "message": f"Couldn't bind photo port {PHOTO_RECEIVE_PORT}: {e}"})
            return
        self.photo_server_socket = server
        while not self.stop_event.is_set():
            try:
                conn, addr = server.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            self.esp32_ip = addr[0]
            threading.Thread(target=self._receive_photo,
                             args=(conn, addr), daemon=True).start()
        try:
            server.close()
        except OSError:
            pass

    # ── Receiving ─────────────────────────────────────────────────────────────
    def _receive_file(self, conn, addr):
        filename  = None
        filepath  = None
        received  = 0
        start_time = time.time()
        try:
            header = b""
            while b"\n" not in header:
                chunk = conn.recv(1)
                if not chunk:
                    return
                header += chunk
            raw_filename, filesize = header.decode().strip().split(":")
            filesize  = int(filesize)
            stamp     = datetime.now().strftime("%Y%m%d_%H%M%S")
            name, ext = os.path.splitext(raw_filename)
            filename  = f"{name}_{stamp}{ext}"
            filepath  = os.path.join(SAVE_FOLDER, filename)
            self.clip_queue.put({"type": "receiving",
                                 "filename": filename, "size_bytes": filesize})
            last_progress = -1
            with open(filepath, "wb") as f:
                while received < filesize:
                    chunk = conn.recv(65536)
                    if not chunk:
                        break
                    f.write(chunk)
                    received += len(chunk)
                    progress = int((received * 100) / filesize) if filesize else 100
                    if progress >= last_progress + 10:
                        last_progress = progress
                        self.clip_queue.put({
                            "type": "progress", "filename": filename,
                            "progress": progress, "elapsed": time.time() - start_time
                        })
        finally:
            conn.close()
        if filename is None:
            return
        elapsed   = time.time() - start_time
        speed_kbs = (received / 1024) / elapsed if elapsed > 0 else 0
        self.clip_queue.put({
            "type": "clip", "filename": filename, "filepath": filepath,
            "size_bytes": received, "ip": addr[0], "received_at": datetime.now(),
            "transfer_seconds": elapsed, "transfer_speed_kbs": speed_kbs,
        })

    def _receive_photo(self, conn, addr):
        self.clip_queue.put({"type": "photo_receiving"})
        received = 0
        filepath = None
        try:
            header = b""
            while b"\n" not in header:
                byte = conn.recv(1)
                if not byte:
                    return
                header += byte
            header_str         = header.decode().strip()
            filename, filesize = header_str.split(":")
            filesize           = int(filesize)
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filepath  = os.path.join(PHOTO_FOLDER, f"photo_{timestamp}.jpg")
            start_time = time.time()
            with open(filepath, "wb") as f:
                while received < filesize:
                    chunk = conn.recv(65536)
                    if not chunk:
                        break
                    f.write(chunk)
                    received += len(chunk)
            elapsed = time.time() - start_time
            self.clip_queue.put({
                "type": "photo_done",
                "filepath": filepath,
                "size": received,
                "elapsed": elapsed,
            })
        finally:
            conn.close()

    # ── Pause / Resume ────────────────────────────────────────────────────────
    def _toggle_pause(self):
        ip = self.esp32_ip
        if not ip:
            self._log("[PAUSE] No ESP32 IP known yet.")
            return
        if self.paused:
            def send_resume():
                try:
                    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                    s.settimeout(5)
                    s.connect((ip, PAUSE_CMD_PORT))
                    s.sendall(b"resume\n")
                    s.close()
                    self.clip_queue.put({"type": "resumed"})
                except Exception as e:
                    self.clip_queue.put({"type": "pause_failed", "message": str(e)})
            threading.Thread(target=send_resume, daemon=True).start()
        else:
            def send_pause():
                try:
                    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                    s.settimeout(5)
                    s.connect((ip, CMD_PORT))
                    s.sendall(b"pause\n")
                    s.close()
                    self.clip_queue.put({"type": "paused"})
                except Exception as e:
                    self.clip_queue.put({"type": "pause_failed", "message": str(e)})
            threading.Thread(target=send_pause, daemon=True).start()

    # ── Take Photo ────────────────────────────────────────────────────────────
    def _request_photo(self):
        ip = self.esp32_ip
        if not ip:
            self._log("[PHOTO] No ESP32 IP known yet — connect first.")
            return
        self._log("[PHOTO] Sending take_photo command to ESP32...")
        self.photo_dot.config(fg=ORANGE)
        self.photo_label.config(text=" Photo: requesting...")
        self.photo_btn.config(state="disabled")

        def send_cmd():
            try:
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.settimeout(5)
                s.connect((ip, PHOTO_CMD_PORT))
                s.sendall(b"take_photo\n")
                s.close()
                self.clip_queue.put({"type": "photo_cmd_sent"})
            except Exception as e:
                self.clip_queue.put({"type": "photo_cmd_failed", "message": str(e)})

        threading.Thread(target=send_cmd, daemon=True).start()

    # ── Queue polling ─────────────────────────────────────────────────────────
    def _poll_queue(self):
        try:
            while True:
                item = self.clip_queue.get_nowait()
                self._handle_queue_item(item)
        except queue.Empty:
            pass
        self.root.after(300, self._poll_queue)

    def _handle_queue_item(self, item):
        t = item["type"]
        if t == "connect":
            self.conn_dot.config(fg=GREEN)
            self.conn_label.config(text=f" ESP32: connected ({item['ip']})")
            self._log(f"Connection from {item['ip']}")
        elif t == "error":
            self._log(f"ERROR: {item['message']}")
        elif t == "receiving":
            self._log(f"Receiving {item['filename']} "
                      f"({item['size_bytes']/1048576:.2f} MB)...")
        elif t == "progress":
            self._log(f"  {item['progress']}% — {item['elapsed']:.1f}s elapsed")
        elif t == "clip":
            self._add_clip(item)
        elif t == "paused":
            self.paused = True
            self.pause_btn.config(text="▶  Resume Recording", bg=GREEN)
            self.pause_dot.config(fg=YELLOW)
            self.pause_label.config(text=" Recording: paused ⏸")
            self._log("[PAUSE] Recording paused.")
        elif t == "resumed":
            self.paused = False
            self.pause_btn.config(text="⏸  Pause Recording", bg=YELLOW)
            self.pause_dot.config(fg=GREEN)
            self.pause_label.config(text=" Recording: running")
            self._log("[PAUSE] Recording resumed.")
        elif t == "pause_failed":
            self._log(f"[PAUSE] Failed: {item['message']}")
        elif t == "photo_cmd_sent":
            self._log("[PHOTO] Command sent — waiting for ESP32...")
            self.photo_label.config(text=" Photo: waiting for capture...")
        elif t == "photo_cmd_failed":
            self._log(f"[PHOTO] Command failed: {item['message']}")
            self.photo_dot.config(fg=RED)
            self.photo_label.config(text=" Photo: command failed")
            self.photo_btn.config(state="normal")
        elif t == "photo_receiving":
            self._log("[PHOTO] Receiving photo...")
            self.photo_dot.config(fg=ORANGE)
            self.photo_label.config(text=" Photo: receiving...")
        elif t == "photo_done":
            size_kb = item["size"] / 1024
            self._log(f"[PHOTO] Saved: {os.path.basename(item['filepath'])} "
                      f"({size_kb:.1f} KB, {item['elapsed']:.1f}s)")
            self.photo_dot.config(fg=GREEN)
            self.photo_label.config(text=" Photo: saved ✓")
            self.photo_btn.config(state="normal")
            try:
                os.startfile(item["filepath"])
            except Exception:
                pass

    def _add_clip(self, item):
        size_mb      = item["size_bytes"] / (1024 * 1024)
        time_str     = item["received_at"].strftime("%Y-%m-%d %H:%M:%S")
        elapsed      = item.get("transfer_seconds", 0)
        speed        = item.get("transfer_speed_kbs", 0)
        transfer_str = f"{elapsed:.1f}s @ {speed:.0f} KB/s"
        iid = self.tree.insert("", "end",
            values=(time_str, item["filename"],
                    f"{size_mb:.2f} MB", transfer_str, "received"))
        self.clips[iid] = item
        self._log(f"Received {item['filename']} — "
                  f"{elapsed:.1f}s, {speed:.0f} KB/s")
        self.pending_iid = iid
        self.pending_label.config(
            text=f"New clip: {item['filename']}\nKeep it, or delete it?",
            fg=ORANGE)
        self.keep_btn.config(state="normal")
        self.delete_btn.config(state="normal")
        self.format_btn.config(state="normal")

    # ── Keep / Delete / Format ────────────────────────────────────────────────
    def _send_command(self, cmd, ip):
        if not ip:
            self._log(f"Cannot send '{cmd}' — no ESP32 IP.")
            return False
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.settimeout(5)
            s.connect((ip, CMD_PORT))
            s.sendall((cmd + "\n").encode())
            s.close()
            self._log(f"Sent '{cmd}' to ESP32 at {ip}")
            return True
        except Exception as e:
            self._log(f"Couldn't send '{cmd}': {e}")
            return False

    def _keep_pending(self):
        self._decide(self.pending_iid, "keep")

    def _delete_pending(self):
        self._decide(self.pending_iid, "delete")

    def _format_sd_pending(self):
        if self.pending_iid is None or self.pending_iid not in self.clips:
            return
        clip = self.clips[self.pending_iid]
        if not messagebox.askyesno("Format SD Card",
                "This will delete ALL files on the ESP32 SD card.\nAre you sure?"):
            return
        self._send_command("format_sd", clip["ip"])
        self.tree.set(self.pending_iid, "status", "SD formatted")
        self.pending_label.config(text="No clip waiting on a decision.", fg=MUTED)
        self.keep_btn.config(state="disabled")
        self.delete_btn.config(state="disabled")
        self.format_btn.config(state="disabled")
        self.pending_iid = None

    def _decide(self, iid, decision):
        if iid is None or iid not in self.clips:
            return
        clip   = self.clips[iid]
        ok     = self._send_command(decision, clip["ip"])
        status = "kept" if decision == "keep" else "deleted"
        if not ok:
            status += " (send failed)"
        self.tree.set(iid, "status", status)
        if iid == self.pending_iid:
            self.pending_label.config(
                text="No clip waiting on a decision.", fg=MUTED)
            self.keep_btn.config(state="disabled")
            self.delete_btn.config(state="disabled")
            self.format_btn.config(state="disabled")
            self.pending_iid = None

    # ── Video playback ────────────────────────────────────────────────────────
    def _selected_clip(self):
        sel = self.tree.selection()
        if not sel:
            return None
        return self.clips.get(sel[0])

    def _play_selected(self):
        clip = self._selected_clip()
        if not clip:
            messagebox.showinfo("Play", "Select a clip in the list first.")
            return
        if not HAVE_CV2:
            messagebox.showinfo("opencv-python needed",
                "Playback needs opencv-python.\n\nRun: pip install opencv-python")
            return
        self._start_playback(clip["filepath"], clip["filename"])

    def _start_playback(self, path, filename):
        self._stop_playback()
        cap = cv2.VideoCapture(path)
        if not cap.isOpened():
            self._log(f"Couldn't open {path}")
            return
        self.cap           = cap
        self.current_path  = path
        self.fps           = cap.get(cv2.CAP_PROP_FPS) or 15
        self.delay_ms      = max(1, int(1000 / self.fps))
        self.frame_count   = max(int(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0), 1)
        self.current_frame = 0
        self.scale.config(to=max(self.frame_count - 1, 1))
        self.playing = True
        self.play_btn.config(text="⏸")
        self.video_title.config(text=filename, fg=GREEN)
        self._player_loop()

    def _player_loop(self):
        if not self.playing or self.cap is None:
            return
        ok, frame = self.cap.read()
        if not ok:
            self._stop_playback()
            return
        self.current_frame += 1
        self._render_frame(frame)
        self._update_progress()
        self.after_id = self.root.after(self.delay_ms, self._player_loop)

    def _render_frame(self, frame):
        if frame.shape[1] != VID_W or frame.shape[0] != VID_H:
            frame = cv2.resize(frame, (VID_W, VID_H))
        rgb   = frame[:, :, ::-1]
        photo = self._make_photo(VID_W, VID_H, rgb.tobytes())
        self.video_label.config(image=photo)
        self.video_label.image = photo

    def _update_progress(self):
        self.updating_slider = True
        self.scale_var.set(self.current_frame)
        self.updating_slider = False
        fps     = self.fps or 1
        cur_s   = self.current_frame / fps
        total_s = self.frame_count / fps
        self.time_label.config(
            text=f"{self._fmt_time(cur_s)} / {self._fmt_time(total_s)}")

    def _on_seek(self, value):
        if self.updating_slider or self.cap is None:
            return
        frame_idx = int(float(value))
        self.cap.set(cv2.CAP_PROP_POS_FRAMES, frame_idx)
        ok, frame = self.cap.read()
        if ok:
            self.current_frame = frame_idx
            self._render_frame(frame)
            self._update_progress()
            self.cap.set(cv2.CAP_PROP_POS_FRAMES, frame_idx)

    def _toggle_play(self):
        if self.cap is None:
            return
        if self.playing:
            self.playing = False
            if self.after_id:
                self.root.after_cancel(self.after_id)
                self.after_id = None
            self.play_btn.config(text="▶")
        else:
            self.playing = True
            self.play_btn.config(text="⏸")
            self._player_loop()

    def _stop_playback(self):
        self.playing = False
        if self.after_id:
            try:
                self.root.after_cancel(self.after_id)
            except Exception:
                pass
            self.after_id = None
        if self.cap:
            self.cap.release()
            self.cap = None
        self.video_label.config(image=self._blank)
        self.video_label.image = self._blank
        self.play_btn.config(text="▶")
        self.current_frame = 0
        self.updating_slider = True
        self.scale_var.set(0)
        self.updating_slider = False
        self.time_label.config(text="0:00 / 0:00")
        if self.current_path:
            name = os.path.basename(self.current_path)
            self.video_title.config(text=f"{name} (stopped)", fg=MUTED)
        else:
            self.video_title.config(text="No clip loaded", fg=MUTED)

    def _open_selected_folder(self):
        clip   = self._selected_clip()
        folder = os.path.dirname(clip["filepath"]) if clip else SAVE_FOLDER
        try:
            if sys.platform.startswith("win"):
                os.startfile(folder)
        except Exception as e:
            self._log(f"Couldn't open folder: {e}")

    def _on_close(self):
        self._stop_playback()
        self._stop_listening()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app  = ReceiverApp(root)
    root.mainloop()
