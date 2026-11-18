#!/usr/bin/env python3
"""
ENIGMA-X  v2  -  digital Enigma machine + Morse messenger, dark GUI.

CIPHER tab     : 3 rotors, rings, positions, reflector, plugboard, key codes,
                 Classic (A-Z) and Extended (A-Z 0-9 + symbols) modes.
MESSENGER tab  : every computer gets its own code (like a phone number).
                 Type a message -> Enigma scrambles it -> it becomes Morse ->
                 the relay delivers it -> the other app PLAYS the Morse and
                 AUTO-DECODES it back to readable text with that contact's key.

Needs only Python + Tkinter. Run enigma_relay.py somewhere both computers
can reach, put its address in the MESSENGER tab, and swap codes + key codes.

NOTE: Enigma is a historical cipher and was broken in WWII. Great for fun and
learning, but don't use it to protect real secrets.
"""
import base64
import json
import math
import os
import queue
import random
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import urllib.error
import urllib.request
import wave
import zlib
from array import array
from pathlib import Path
from tkinter import ttk

# ----------------------------------------------------------------- palette
BG = "#0b0e14"
PANEL = "#121722"
PANEL2 = "#090c12"
EDGE = "#222b3b"
TEXT = "#c9d1d9"
DIM = "#667184"
AMBER = "#ffb454"
CYAN = "#39d0ff"
RED = "#ff6b6b"
GREEN = "#3ddc84"

CONFIG_DIR = Path(os.environ.get("ENIGMA_X_HOME", str(Path.home() / ".enigma_x")))
DEFAULT_SERVER = "http://127.0.0.1:8765"

# ------------------------------------------------------------- alphabets
CLASSIC = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
EXTENDED = CLASSIC + "0123456789 .,?!-:/"  # 44 symbols (even, needed for reflector)

HIST_ROTORS = {  # name: (wiring, notch letter)
    "I": ("EKMFLGDQVZNTOWYHXUSPAIBRCJ", "Q"),
    "II": ("AJDKSIRUXBLHWTMCQGZNPYFVOE", "E"),
    "III": ("BDFHJLCPRTXVZNYEIWGAKMUSQO", "V"),
    "IV": ("ESOVPZJAYQUIRHXLNFTGKDCMWB", "J"),
    "V": ("VZBRGITYUPSDNHLXAWMJQOFECK", "Z"),
}
HIST_REFLECTORS = {
    "B": "YRUHQSLDPXNGOKMIEBFZCWVJAT",
    "C": "FVPJIAOYEDRZXWGCTKUQSBNMHL",
}


def build_profiles():
    classic = {
        "alphabet": CLASSIC,
        "plugchars": CLASSIC,
        "rotors": {k: ([CLASSIC.index(c) for c in w], CLASSIC.index(nt))
                   for k, (w, nt) in HIST_ROTORS.items()},
        "reflectors": {k: [CLASSIC.index(c) for c in w]
                       for k, w in HIST_REFLECTORS.items()},
    }
    rng = random.Random(1943)  # fixed seed => same machine on every computer
    n = len(EXTENDED)
    rotors, refls = {}, {}
    for name in HIST_ROTORS:
        perm = list(range(n))
        rng.shuffle(perm)
        rotors[name] = (perm, rng.randrange(n))
    for name in HIST_REFLECTORS:
        idx = list(range(n))
        rng.shuffle(idx)
        m = [0] * n
        for i in range(0, n, 2):
            a, b = idx[i], idx[i + 1]
            m[a], m[b] = b, a
        refls[name] = m
    extended = {
        "alphabet": EXTENDED,
        "plugchars": EXTENDED[:36],  # letters + digits
        "rotors": rotors,
        "reflectors": refls,
    }
    return {"classic": classic, "extended": extended}


PROFILES = build_profiles()


def disp(c):
    return "\u2423" if c == " " else c


# ---------------------------------------------------------------- machine
class Enigma:
    def __init__(self, profile, order, positions, rings, reflector, plug_pairs):
        self.alpha = profile["alphabet"]
        self.n = len(self.alpha)
        self.index = {c: i for i, c in enumerate(self.alpha)}
        self.fwd, self.inv, self.notch = [], [], []
        for name in order:  # order = [left, middle, right]
            perm, notch = profile["rotors"][name]
            inv = [0] * self.n
            for i, v in enumerate(perm):
                inv[v] = i
            self.fwd.append(perm)
            self.inv.append(inv)
            self.notch.append(notch)
        self.pos = list(positions)
        self.rings = list(rings)
        self.refl = profile["reflectors"][reflector]
        self.plug = list(range(self.n))
        for a, b in plug_pairs:
            ia, ib = self.index[a], self.index[b]
            self.plug[ia], self.plug[ib] = ib, ia
        self.last_out = None

    def _step(self):
        n, p = self.n, self.pos
        if p[1] == self.notch[1]:  # double step
            p[0] = (p[0] + 1) % n
            p[1] = (p[1] + 1) % n
        elif p[2] == self.notch[2]:
            p[1] = (p[1] + 1) % n
        p[2] = (p[2] + 1) % n

    def _rotor(self, i, c, forward):
        shift = self.pos[i] - self.rings[i]
        c = (c + shift) % self.n
        c = (self.fwd[i] if forward else self.inv[i])[c]
        return (c - shift) % self.n

    def _char(self, c):
        self._step()
        c = self.plug[c]
        for i in (2, 1, 0):
            c = self._rotor(i, c, True)
        c = self.refl[c]
        for i in (0, 1, 2):
            c = self._rotor(i, c, False)
        return self.plug[c]

    def process(self, text):
        out = []
        for ch in text.upper():
            if ch in self.index:
                o = self.alpha[self._char(self.index[ch])]
                self.last_out = o
                out.append(o)
            else:
                out.append(ch)  # anything outside the alphabet passes through
        return "".join(out)


def run_cfg(cfg, text, offset=None):
    """Encrypt/decrypt text with a settings dict. `offset` is the per-message
    key: three numbers added to the rotor start positions so no two messages
    start from exactly the same place."""
    p = PROFILES[cfg["m"]]
    n = len(p["alphabet"])
    pos = list(cfg["p"])
    if offset:
        pos = [(a + b) % n for a, b in zip(pos, offset)]
    return Enigma(p, cfg["o"], pos, cfg["r"], cfg["f"], cfg["s"]).process(text)


# ------------------------------------------------------------ key codes
def encode_key(cfg):
    raw = zlib.compress(json.dumps(cfg, separators=(",", ":")).encode())
    return "ENX1-" + base64.urlsafe_b64encode(raw).decode().rstrip("=")


def decode_key(s):
    s = s.strip()
    if not s.startswith("ENX1-"):
        raise ValueError("That doesn't look like an ENX1 key code")
    body = s[5:]
    body += "=" * (-len(body) % 4)
    try:
        return json.loads(zlib.decompress(base64.urlsafe_b64decode(body)))
    except Exception:
        raise ValueError("Key code is damaged or incomplete")


# ---------------------------------------------------------------- morse
MORSE = {
    "A": ".-", "B": "-...", "C": "-.-.", "D": "-..", "E": ".", "F": "..-.",
    "G": "--.", "H": "....", "I": "..", "J": ".---", "K": "-.-", "L": ".-..",
    "M": "--", "N": "-.", "O": "---", "P": ".--.", "Q": "--.-", "R": ".-.",
    "S": "...", "T": "-", "U": "..-", "V": "...-", "W": ".--", "X": "-..-",
    "Y": "-.--", "Z": "--..",
    "0": "-----", "1": ".----", "2": "..---", "3": "...--", "4": "....-",
    "5": ".....", "6": "-....", "7": "--...", "8": "---..", "9": "----.",
    ".": ".-.-.-", ",": "--..--", "?": "..--..", "!": "-.-.--", "-": "-....-",
    ":": "---...", "/": "-..-.",
}
MORSE_REV = {v: k for k, v in MORSE.items()}


def to_morse(text):
    """Letters are separated by a space, words by a '|'. Characters Morse has
    no symbol for are dropped."""
    tokens = []
    for ch in text.upper():
        if ch.isspace():
            tokens.append("|")
        elif ch in MORSE:
            tokens.append(MORSE[ch])
    return " ".join(tokens)


def from_morse(m):
    out = []
    for tok in m.split():
        out.append(" " if tok == "|" else MORSE_REV.get(tok, "#"))
    return "".join(out)


def morse_timeline(morse, wpm):
    """Returns ([(start, end), ...] seconds for every tone, total seconds)."""
    unit = 1.2 / max(wpm, 1)
    t, events = 0.0, []
    for tok in morse.split():
        if tok == "|":
            t += unit * 4  # + the 3 after the previous letter = 7
            continue
        for i, el in enumerate(tok):
            d = unit * (1 if el == "." else 3)
            events.append((t, t + d))
            t += d
            if i < len(tok) - 1:
                t += unit
        t += unit * 3
    return events, t


def make_wav(events, total, freq=620, rate=8000):
    n = int((total + 0.25) * rate)
    buf = array("h", [0]) * n
    fade = int(0.006 * rate)
    for s, e in events:
        i0, i1 = int(s * rate), min(int(e * rate), n)
        for i in range(i0, i1):
            k = min(i - i0, i1 - i - 1)
            amp = 1.0 if k >= fade else k / fade
            buf[i] = int(15000 * amp * math.sin(2 * math.pi * freq * i / rate))
    fd, path = tempfile.mkstemp(suffix=".wav", prefix="enx_")
    os.close(fd)
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        if sys.byteorder == "big":
            buf.byteswap()
        w.writeframes(buf.tobytes())
    return path


def play_wav(path):
    """Plays a wav with whatever the OS already has. Returns False if it can't."""
    try:
        if sys.platform.startswith("win"):
            import winsound
            winsound.PlaySound(path, winsound.SND_FILENAME)
            return True
        if sys.platform == "darwin":
            subprocess.run(["afplay", path], check=True)
            return True
        for cmd in (["paplay"], ["aplay", "-q"], ["play", "-q"],
                    ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"]):
            if shutil.which(cmd[0]):
                try:
                    subprocess.run(cmd + [path], check=True, stdout=subprocess.DEVNULL,
                                   stderr=subprocess.DEVNULL)
                    return True
                except Exception:
                    continue  # try the next player
    except Exception:
        pass
    return False


class Player(threading.Thread):
    """Plays Morse one message at a time, and tells the UI when to flash."""

    def __init__(self, ui_q, is_muted):
        super().__init__(daemon=True)
        self.q = queue.Queue()
        self.ui_q = ui_q
        self.is_muted = is_muted

    def enqueue(self, morse, wpm):
        self.q.put((morse, wpm))

    def run(self):
        while True:
            morse, wpm = self.q.get()
            events, total = morse_timeline(morse, wpm)
            if not events:
                continue
            played = False
            if not self.is_muted():
                path = make_wav(events, total)
                self.ui_q.put(("lamp", events))
                played = play_wav(path)
                try:
                    os.remove(path)
                except OSError:
                    pass
                if not played:
                    self.ui_q.put(("noplayer", None))
            else:
                self.ui_q.put(("lamp", events))
            if not played:
                time.sleep(total)


# -------------------------------------------------------------- network
ID_CHARS = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"


def canon(s):
    return re.sub(r"[^A-Z0-9]", "", str(s).upper())


def show_code(c):
    c = canon(c)
    return c[:3] + "-" + c[3:] if len(c) > 3 else c


def load_json(name, default):
    try:
        return json.loads((CONFIG_DIR / name).read_text())
    except Exception:
        return default


def save_json(name, data):
    try:
        CONFIG_DIR.mkdir(parents=True, exist_ok=True)
        (CONFIG_DIR / name).write_text(json.dumps(data, indent=1))
    except Exception:
        pass


class Net:
    """Long-polls the relay for incoming messages and sends outgoing ones."""

    def __init__(self, ui_q, cfg):
        self.ui_q = ui_q
        self.cfg = cfg
        self.gen = 0

    def _headers(self):
        return {"X-Id": self.cfg["id"], "X-Token": self.cfg["token"]}

    def restart(self):
        self.gen += 1
        threading.Thread(target=self._loop, args=(self.gen,), daemon=True).start()

    def _loop(self, gen):
        backoff = 1
        wait = 0  # first poll returns instantly so the status light updates right away
        while gen == self.gen:
            try:
                req = urllib.request.Request(
                    self.cfg["server"].rstrip("/") + f"/poll?wait={wait}",
                    headers=self._headers())
                with urllib.request.urlopen(req, timeout=35) as r:
                    data = json.loads(r.read())
                for m in data.get("messages", []):  # never drop a message, even from an old poll
                    self.ui_q.put(("msg", m))
                if gen != self.gen:
                    return
                self.ui_q.put(("net", "online"))
                backoff, wait = 1, 20
            except urllib.error.HTTPError as e:
                self.ui_q.put(("net", "taken" if e.code == 403 else "offline"))
                time.sleep(min(backoff, 15))
                backoff *= 2
            except Exception:
                if gen != self.gen:
                    return
                self.ui_q.put(("net", "offline"))
                time.sleep(min(backoff, 15))
                backoff *= 2

    def send(self, to, morse, wpm, mk, key_code):
        def run():
            # Include the exact machine settings used for this message so the
            # recipient can decode it even when accepting a brand-new contact.
            body = json.dumps({
                "to": to, "morse": morse, "wpm": wpm, "mk": mk, "key": key_code
            }).encode()
            hdr = dict(self._headers(), **{"Content-Type": "application/json"})
            try:
                req = urllib.request.Request(
                    self.cfg["server"].rstrip("/") + "/send", data=body,
                    headers=hdr, method="POST")
                urllib.request.urlopen(req, timeout=15).read()
                self.ui_q.put(("sent", to))
            except urllib.error.HTTPError as e:
                try:
                    err = json.loads(e.read()).get("error", f"error {e.code}")
                except Exception:
                    err = f"error {e.code}"
                self.ui_q.put(("senderr", err))
            except Exception:
                self.ui_q.put(("senderr", "Can't reach the relay server"))
        threading.Thread(target=run, daemon=True).start()


# ------------------------------------------------------------- rotor UI
class RotorUI(tk.Frame):
    def __init__(self, master, title, on_change):
        super().__init__(master, bg=PANEL)
        self.name = tk.StringVar()
        self.pos = tk.IntVar(value=0)
        self.ring = tk.StringVar()
        self.on_change = on_change
        self.alpha = CLASSIC

        tk.Label(self, text=title, bg=PANEL, fg=DIM,
                 font=("Consolas", 9, "bold")).pack(pady=(0, 4))
        self.combo = ttk.Combobox(self, textvariable=self.name, state="readonly",
                                  width=5, justify="center")
        self.combo.pack()
        self.up = self._arrow("\u25b2", 1)
        self.win = tk.Label(self, font=("Consolas", 38, "bold"), fg=AMBER,
                            bg=PANEL2, width=2, highlightthickness=2,
                            highlightbackground=EDGE, highlightcolor=EDGE)
        self.win.pack(pady=2)
        self.dn = self._arrow("\u25bc", -1)
        tk.Label(self, text="RING", bg=PANEL, fg=DIM,
                 font=("Consolas", 8)).pack(pady=(8, 0))
        self.ring_combo = ttk.Combobox(self, textvariable=self.ring,
                                       state="readonly", width=3, justify="center")
        self.ring_combo.pack()

        self.win.bind("<MouseWheel>", lambda e: self.bump(1 if e.delta > 0 else -1))
        self.win.bind("<Button-4>", lambda e: self.bump(1))
        self.win.bind("<Button-5>", lambda e: self.bump(-1))
        self.name.trace_add("write", lambda *_: self.on_change())
        self.ring.trace_add("write", lambda *_: self.on_change())
        self.pos.trace_add("write", lambda *_: self._draw())

    def _arrow(self, sym, d):
        b = tk.Button(self, text=sym, command=lambda: self.bump(d), bg=PANEL,
                      fg=CYAN, activebackground=EDGE, activeforeground=CYAN,
                      relief="flat", bd=0, font=("Consolas", 10), cursor="hand2")
        b.pack()
        return b

    def _draw(self):
        self.win.config(text=disp(self.alpha[self.pos.get() % len(self.alpha)]))
        self.on_change()

    def bump(self, d):
        self.pos.set((self.pos.get() + d) % len(self.alpha))

    def configure_alphabet(self, alpha, names):
        self.alpha = alpha
        self.combo["values"] = names
        self.ring_combo["values"] = [disp(c) for c in alpha]
        self.pos.set(0)
        self.ring.set(disp(alpha[0]))
        self._draw()

    def ring_index(self):
        for i, c in enumerate(self.alpha):
            if disp(c) == self.ring.get():
                return i
        return 0

    def set_ring(self, i):
        self.ring.set(disp(self.alpha[i]))


# ------------------------------------------------------------ messenger
class MessengerTab(tk.Frame):
    def __init__(self, master, app):
        super().__init__(master, bg=BG)
        self.app = app
        self.contacts = load_json("contacts.json", {})
        self.pending = {}
        self.to_var = tk.StringVar()
        self.name_var = tk.StringVar()
        self.server_var = tk.StringVar(value=app.cfg["server"])
        self.wpm = tk.IntVar(value=app.cfg.get("wpm", 15))
        self.auto = tk.BooleanVar(value=True)
        self.mute = tk.BooleanVar(value=False)
        self.preview = tk.BooleanVar(value=True)
        self.code_var = tk.StringVar(value=show_code(app.cfg["id"]))
        self.net_var = tk.StringVar(value="\u25cf offline")
        self.muted = False
        self.mute.trace_add("write", lambda *_: setattr(self, "muted", bool(self.mute.get())))
        self.player = Player(app.ui_q, lambda: self.muted)
        self.player.start()
        self._build()
        self.refresh_contacts()

    # -- widgets
    def _entry(self, parent, var, fg=TEXT, font=("Consolas", 11)):
        return tk.Entry(parent, textvariable=var, bg=PANEL2, fg=fg,
                        insertbackground=CYAN, relief="flat", font=font,
                        highlightthickness=1, highlightbackground=EDGE,
                        highlightcolor=CYAN)

    def _build(self):
        top = tk.Frame(self, bg=PANEL, highlightthickness=1, highlightbackground=EDGE)
        top.pack(fill="x", padx=24, pady=(10, 6))
        tk.Label(top, text="YOUR COMPUTER CODE", bg=PANEL, fg=DIM,
                 font=("Consolas", 9, "bold")).grid(row=0, column=0, sticky="w", padx=16, pady=(10, 0))
        tk.Label(top, textvariable=self.code_var, bg=PANEL, fg=CYAN,
                 font=("Consolas", 28, "bold")).grid(row=1, column=0, sticky="w", padx=16, pady=(0, 10))
        self.app.button(top, "Copy code", self.copy_code).grid(row=1, column=1, padx=6)
        tk.Label(top, text="RELAY SERVER", bg=PANEL, fg=DIM,
                 font=("Consolas", 9, "bold")).grid(row=0, column=2, sticky="w", padx=(30, 0), pady=(10, 0))
        self._entry(top, self.server_var).grid(row=1, column=2, sticky="ew", padx=(30, 6), ipady=5)
        self.app.button(top, "Connect", self.connect, True).grid(row=1, column=3, padx=(0, 6))
        self.net_lbl = tk.Label(top, textvariable=self.net_var, bg=PANEL, fg=RED,
                                font=("Consolas", 11, "bold"))
        self.net_lbl.grid(row=1, column=4, padx=(6, 16))
        top.columnconfigure(2, weight=1)

        self.banner = tk.Frame(self, bg="#2a2112", highlightthickness=1,
                               highlightbackground=AMBER)
        self.banner_lbl = tk.Label(self.banner, text="", bg="#2a2112", fg=AMBER,
                                   font=("Consolas", 11, "bold"))
        self.banner_lbl.pack(side="left", padx=12, pady=8)
        self.app.button(self.banner, "Block", self.block_pending).pack(side="right", padx=8, pady=6)
        self.app.button(self.banner, "Accept", self.accept_pending, True).pack(side="right", pady=6)

        body = tk.Frame(self, bg=BG)
        self.body = body
        body.pack(fill="both", expand=True, padx=24, pady=4)
        body.columnconfigure(1, weight=1)
        body.rowconfigure(0, weight=1)

        # contacts
        left = tk.Frame(body, bg=PANEL, highlightthickness=1, highlightbackground=EDGE, width=290)
        left.grid(row=0, column=0, sticky="ns", padx=(0, 10))
        left.pack_propagate(False)
        tk.Label(left, text="CONTACTS", bg=PANEL, fg=DIM,
                 font=("Consolas", 9, "bold")).pack(anchor="w", padx=12, pady=(10, 4))
        self.listbox = tk.Listbox(left, bg=PANEL2, fg=TEXT, relief="flat",
                                  selectbackground="#1d3b53", selectforeground=TEXT,
                                  font=("Consolas", 11), highlightthickness=1,
                                  highlightbackground=EDGE, exportselection=False, height=8)
        self.listbox.pack(fill="both", expand=True, padx=12)
        self.listbox.bind("<<ListboxSelect>>", self.on_select)
        tk.Label(left, text="Their name", bg=PANEL, fg=DIM,
                 font=("Consolas", 9)).pack(anchor="w", padx=12, pady=(8, 0))
        self._entry(left, self.name_var).pack(fill="x", padx=12, ipady=4)
        tk.Label(left, text="Their computer code", bg=PANEL, fg=DIM,
                 font=("Consolas", 9)).pack(anchor="w", padx=12, pady=(6, 0))
        self._entry(left, self.to_var, AMBER, ("Consolas", 13, "bold")).pack(fill="x", padx=12, ipady=4)
        row = tk.Frame(left, bg=PANEL)
        row.pack(fill="x", padx=12, pady=8)
        self.app.button(row, "Save + use current key", self.save_contact).pack(fill="x")
        row2 = tk.Frame(left, bg=PANEL)
        row2.pack(fill="x", padx=12, pady=(0, 10))
        self.app.button(row2, "Block", self.toggle_block).pack(side="left", expand=True, fill="x", padx=(0, 3))
        self.app.button(row2, "Remove", self.remove_contact).pack(side="left", expand=True, fill="x", padx=(3, 0))

        # right: log + compose
        right = tk.Frame(body, bg=BG)
        right.grid(row=0, column=1, sticky="nsew")
        right.rowconfigure(1, weight=1)
        right.columnconfigure(0, weight=1)
        head = tk.Frame(right, bg=BG)
        head.grid(row=0, column=0, sticky="ew")
        tk.Label(head, text="MESSAGES  (incoming are decoded for you)", bg=BG, fg=DIM,
                 font=("Consolas", 9, "bold")).pack(side="left")
        self.lamp = tk.Canvas(head, width=34, height=34, bg=BG, highlightthickness=0)
        self.lamp.pack(side="right")
        self._lamp_glow = self.lamp.create_oval(2, 2, 32, 32, fill="#3a2a10", outline="", state="hidden")
        self._lamp_dot = self.lamp.create_oval(8, 8, 26, 26, fill=PANEL, outline=EDGE, width=2)
        tk.Checkbutton(head, text="Mute", variable=self.mute, bg=BG, fg=TEXT, selectcolor=PANEL2,
                       activebackground=BG, activeforeground=CYAN,
                       font=("Consolas", 9)).pack(side="right", padx=4)
        tk.Checkbutton(head, text="Auto-play", variable=self.auto, bg=BG, fg=TEXT, selectcolor=PANEL2,
                       activebackground=BG, activeforeground=CYAN,
                       font=("Consolas", 9)).pack(side="right", padx=4)

        self.log = tk.Text(right, bg=PANEL2, fg=TEXT, relief="flat", wrap="word",
                           font=("Consolas", 12), padx=12, pady=10, highlightthickness=1,
                           highlightbackground=EDGE, highlightcolor=CYAN, height=10,
                           state="disabled")
        self.log.grid(row=1, column=0, sticky="nsew")
        self.log.tag_config("meta", foreground=DIM, font=("Consolas", 9))
        self.log.tag_config("morse", foreground="#4a5568", font=("Consolas", 9))
        self.log.tag_config("in", foreground=AMBER, font=("Consolas", 14, "bold"))
        self.log.tag_config("out", foreground=CYAN, font=("Consolas", 14, "bold"))
        self.log.tag_config("err", foreground=RED, font=("Consolas", 11))

        comp = tk.Frame(right, bg=BG)
        comp.grid(row=2, column=0, sticky="ew", pady=(8, 0))
        comp.columnconfigure(0, weight=1)
        self.compose = tk.Text(comp, bg=PANEL2, fg=TEXT, insertbackground=CYAN,
                               relief="flat", font=("Consolas", 13), wrap="word", height=3,
                               padx=10, pady=8, highlightthickness=1,
                               highlightbackground=EDGE, highlightcolor=CYAN)
        self.compose.grid(row=0, column=0, sticky="ew")
        self.compose.bind("<Control-Return>", lambda e: (self.send(), "break")[1])
        side = tk.Frame(comp, bg=BG)
        side.grid(row=0, column=1, padx=(8, 0), sticky="ns")
        self.app.button(side, "SEND MORSE \u25b6", self.send, True).pack(fill="x")
        tk.Checkbutton(side, text="Play my own", variable=self.preview, bg=BG, fg=TEXT,
                       selectcolor=PANEL2, activebackground=BG, activeforeground=CYAN,
                       font=("Consolas", 9)).pack(anchor="w")
        wp = tk.Frame(comp, bg=BG)
        wp.grid(row=1, column=0, sticky="w", pady=(4, 0))
        tk.Label(wp, text="SPEED (wpm)", bg=BG, fg=DIM, font=("Consolas", 9, "bold")).pack(side="left")
        tk.Scale(wp, from_=8, to=30, orient="horizontal", variable=self.wpm, length=200,
                 bg=BG, fg=CYAN, troughcolor=EDGE, highlightthickness=0, bd=0,
                 sliderrelief="flat", sliderlength=22, width=12, showvalue=True,
                 activebackground=CYAN, font=("Consolas", 9, "bold")).pack(side="left", padx=8)
        tk.Label(wp, text="Ctrl+Enter sends", bg=BG, fg=DIM, font=("Consolas", 9)).pack(side="left", padx=8)

    # -- helpers
    def say(self, who, plain, morse="", kind="in", note=""):
        self.log.config(state="normal")
        stamp = time.strftime("%H:%M")
        self.log.insert("end", f"{who}  {stamp}  {note}\n", "meta")
        if morse:
            shown = morse if len(morse) < 160 else morse[:157] + "..."
            self.log.insert("end", shown + "\n", "morse")
        self.log.insert("end", plain + "\n\n", kind)
        self.log.see("end")
        self.log.config(state="disabled")

    def name_of(self, code):
        c = self.contacts.get(code)
        return f"{c['name']} ({show_code(code)})" if c and c.get("name") and c["name"] != code else show_code(code)

    def refresh_contacts(self):
        self.listbox.delete(0, "end")
        self.order = sorted(self.contacts, key=lambda k: self.contacts[k].get("name", k).lower())
        for code in self.order:
            c = self.contacts[code]
            flag = "  \u2715 blocked" if c.get("blocked") else ""
            self.listbox.insert("end", f"{c.get('name', code)}  {show_code(code)}{flag}")
        save_json("contacts.json", self.contacts)

    def current_contact(self):
        sel = self.listbox.curselection()
        return self.order[sel[0]] if sel else None

    # -- contacts
    def on_select(self, _e=None):
        code = self.current_contact()
        if not code:
            return
        c = self.contacts[code]
        self.to_var.set(show_code(code))
        self.name_var.set(c.get("name", ""))
        if c.get("key"):
            try:
                self.app.apply_cfg(decode_key(c["key"]))
                self.app.status(f"Loaded the key for {c.get('name', code)}.")
            except Exception:
                pass

    def save_contact(self):
        code = canon(self.to_var.get())
        if len(code) < 3:
            self.app.status("Type their computer code first.", err=True)
            return
        try:
            key = encode_key(self.app.collect())
        except ValueError as e:
            self.app.status(str(e), err=True)
            return
        name = self.name_var.get().strip() or show_code(code)
        self.contacts[code] = {"name": name, "key": key, "blocked": False}
        self.refresh_contacts()
        self.app.status(f"Saved {name}. Messages with them now use the machine setup shown in the CIPHER tab.")

    def toggle_block(self):
        code = self.current_contact()
        if code:
            self.contacts[code]["blocked"] = not self.contacts[code].get("blocked")
            self.refresh_contacts()

    def remove_contact(self):
        code = self.current_contact()
        if code:
            del self.contacts[code]
            self.refresh_contacts()

    # -- network
    def copy_code(self):
        self.clipboard_clear()
        self.clipboard_append(self.code_var.get())
        self.app.status("Your computer code was copied. Send it to your friend.")

    def connect(self):
        url = self.server_var.get().strip()
        if not url.startswith("http"):
            url = "http://" + url
            self.server_var.set(url)
        self.app.cfg["server"] = url
        self.app.cfg["wpm"] = self.wpm.get()
        save_json("config.json", self.app.cfg)
        self.net_var.set("\u25cf connecting...")
        self.net_lbl.config(fg=AMBER)
        self.app.net.restart()

    def handle(self, kind, val):
        if kind == "net":
            if val == "online":
                self.net_var.set("\u25cf online")
                self.net_lbl.config(fg=GREEN)
            elif val == "taken":
                self.app.cfg["id"] = "".join(secrets.choice(ID_CHARS) for _ in range(6))
                self.app.cfg["token"] = secrets.token_hex(16)
                save_json("config.json", self.app.cfg)
                self.code_var.set(show_code(self.app.cfg["id"]))
                self.app.net.restart()
                self.app.status("That code was already taken on the relay, so you got a new one.", err=True)
            else:
                self.net_var.set("\u25cf offline")
                self.net_lbl.config(fg=RED)
        elif kind == "msg":
            self.incoming(val)
        elif kind == "sent":
            self.app.status(f"Delivered to the relay for {show_code(val)}.")
        elif kind == "senderr":
            self.app.status(f"Not sent: {val}", err=True)
            self.say("system", f"Not sent: {val}", kind="err")
        elif kind == "lamp":
            self.flash_events(val)
        elif kind == "noplayer":
            self.app.status("No audio player found on this computer, so you get the light only.", err=True)

    def flash_events(self, events):
        for s, e in events:
            self.after(int(s * 1000), self._lamp, True)
            self.after(int(e * 1000), self._lamp, False)

    def _lamp(self, on):
        self.lamp.itemconfig(self._lamp_glow, state="normal" if on else "hidden")
        self.lamp.itemconfig(self._lamp_dot, fill=AMBER if on else PANEL,
                             outline="#ffd9a0" if on else EDGE)

    # -- receiving
    def incoming(self, m):
        code = canon(m.get("from", ""))
        c = self.contacts.get(code)
        if c and c.get("blocked"):
            return
        if not c:
            self.pending.setdefault(code, []).append(m)
            self.show_banner()
            return
        self.deliver(code, m)

    def deliver(self, code, m):
        morse = m.get("morse", "")
        cipher = from_morse(morse)
        c = self.contacts.get(code, {})
        note = ""
        try:
            # New messages carry the exact key used by the sender. Prefer it
            # over a saved contact key so key changes cannot cause gibberish.
            message_key = m.get("key")
            if message_key:
                cfg = decode_key(message_key)
                c["key"] = message_key
                self.contacts[code] = c
                save_json("contacts.json", self.contacts)
            elif c.get("key"):
                cfg = decode_key(c["key"])
            else:
                # Backward compatibility with messages from older app versions.
                cfg = self.app.collect()
                note = "(legacy message: used your current machine setup)"
            plain = run_cfg(cfg, cipher, m.get("mk"))
        except Exception:
            plain, note = "[could not decrypt - check you share the same key code]", "(cipher: " + cipher + ")"
        self.say(self.name_of(code), plain, morse, "in", note)
        if self.auto.get():
            self.player.enqueue(morse, int(m.get("wpm", 15)))

    def show_banner(self):
        if not self.pending:
            self.banner.pack_forget()
            return
        code = next(iter(self.pending))
        n = len(self.pending[code])
        self.banner_lbl.config(text=f"{show_code(code)} wants to message you  ({n} waiting)")
        self.banner.pack(fill="x", padx=24, pady=(0, 6), before=self.body)

    def accept_pending(self):
        if not self.pending:
            return
        code = next(iter(self.pending))
        msgs = self.pending.pop(code)
        # Save the sender's actual message key when available. Do not guess
        # by saving the recipient's current machine settings.
        key = next((m.get("key") for m in msgs if m.get("key")), None)
        if key:
            try:
                decode_key(key)  # reject malformed key codes
            except Exception:
                key = None
        self.contacts[code] = {"name": show_code(code), "key": key, "blocked": False}
        self.refresh_contacts()
        for m in msgs:
            self.deliver(code, m)
        self.show_banner()

    def block_pending(self):
        if not self.pending:
            return
        code = next(iter(self.pending))
        self.pending.pop(code)
        self.contacts[code] = {"name": show_code(code), "key": None, "blocked": True}
        self.refresh_contacts()
        self.show_banner()

    # -- sending
    def send(self):
        to = canon(self.to_var.get())
        plain = self.compose.get("1.0", "end-1c").strip()
        if len(to) < 3 or not plain:
            self.app.status("Type their computer code and a message first.", err=True)
            return
        c = self.contacts.get(to)
        try:
            cfg = decode_key(c["key"]) if c and c.get("key") else self.app.collect()
        except ValueError as e:
            self.app.status(str(e), err=True)
            return
        n = len(PROFILES[cfg["m"]]["alphabet"])
        mk = [secrets.randbelow(n) for _ in range(3)]
        cipher = run_cfg(cfg, plain, mk)
        morse = to_morse(cipher)
        if not morse:
            self.app.status("Nothing Morse can carry in that message.", err=True)
            return
        wpm = self.wpm.get()
        self.app.net.send(to, morse, wpm, mk, encode_key(cfg))
        self.say("you \u2192 " + self.name_of(to), plain, morse, "out",
                 "" if c and c.get("key") else "(used your current machine setup)")
        self.compose.delete("1.0", "end")
        if self.preview.get() and self.auto.get():
            self.player.enqueue(morse, wpm)


# ------------------------------------------------------------------ app
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("ENIGMA-X  //  digital cipher machine")
        self.geometry("1080x900")
        self.minsize(960, 800)
        self.configure(bg=BG)
        self.ready = False
        self._pending = False
        self.rng = random.SystemRandom()
        self.mode = tk.StringVar(value="classic")
        self.refl_var = tk.StringVar()
        self.plug_var = tk.StringVar()
        self.key_var = tk.StringVar()
        self.live = tk.BooleanVar(value=True)
        self.lamps = {}
        self.ui_q = queue.Queue()

        self.cfg = load_json("config.json", {})
        self.cfg.setdefault("server", DEFAULT_SERVER)
        self.cfg.setdefault("wpm", 15)
        if not self.cfg.get("id") or not self.cfg.get("token"):
            self.cfg["id"] = "".join(secrets.choice(ID_CHARS) for _ in range(6))
            self.cfg["token"] = secrets.token_hex(16)
        save_json("config.json", self.cfg)
        self.net = Net(self.ui_q, self.cfg)

        self._style()
        self._build()
        self.ready = True
        self.apply_mode()
        self.randomize()
        self.net.restart()
        self.after(120, self._pump)

    def _pump(self):
        try:
            while True:
                kind, val = self.ui_q.get_nowait()
                self.msg_tab.handle(kind, val)
        except queue.Empty:
            pass
        self.after(120, self._pump)

    # ---- styling
    def _style(self):
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure("TCombobox", fieldbackground=PANEL2, background=EDGE,
                     foreground=TEXT, arrowcolor=CYAN, bordercolor=EDGE,
                     lightcolor=EDGE, darkcolor=EDGE,
                     selectbackground=PANEL2, selectforeground=TEXT)
        st.map("TCombobox",
               fieldbackground=[("readonly", PANEL2)],
               foreground=[("readonly", TEXT)],
               selectbackground=[("readonly", PANEL2)],
               selectforeground=[("readonly", TEXT)])
        st.configure("TNotebook", background=BG, borderwidth=0, bordercolor=BG,
                     lightcolor=BG, darkcolor=BG, tabmargins=(24, 4, 24, 0))
        st.configure("TNotebook.Tab", background=PANEL, foreground=DIM,
                     padding=(22, 9), font=("Consolas", 10, "bold"), borderwidth=0,
                     bordercolor=BG, lightcolor=PANEL, darkcolor=PANEL)
        self.option_add("*Checkbutton.highlightThickness", 0)
        self.option_add("*Radiobutton.highlightThickness", 0)
        self.option_add("*Button.highlightThickness", 0)
        self.option_add("*Checkbutton.borderWidth", 0)
        st.map("TNotebook.Tab", background=[("selected", PANEL2)],
               foreground=[("selected", CYAN)])
        self.option_add("*TCombobox*Listbox.background", PANEL2)
        self.option_add("*TCombobox*Listbox.foreground", TEXT)
        self.option_add("*TCombobox*Listbox.selectBackground", CYAN)
        self.option_add("*TCombobox*Listbox.selectForeground", BG)
        self.option_add("*TCombobox*Listbox.font", ("Consolas", 10))

    def button(self, parent, text, cmd, accent=False):
        bg, fg = (CYAN, BG) if accent else (EDGE, TEXT)
        hover = "#7ae3ff" if accent else "#2e3a50"
        b = tk.Button(parent, text=text, command=cmd, bg=bg, fg=fg,
                      activebackground=hover, activeforeground=fg,
                      relief="flat", bd=0, padx=14, pady=7, cursor="hand2",
                      font=("Consolas", 10, "bold"))
        b.bind("<Enter>", lambda e: b.config(bg=hover))
        b.bind("<Leave>", lambda e: b.config(bg=bg))
        return b

    # ---- layout
    def _build(self):
        head = tk.Frame(self, bg=BG)
        head.pack(fill="x", padx=24, pady=(16, 4))
        tk.Label(head, text="ENIGMA", bg=BG, fg=TEXT,
                 font=("Consolas", 26, "bold")).pack(side="left")
        tk.Label(head, text="-X", bg=BG, fg=CYAN,
                 font=("Consolas", 26, "bold")).pack(side="left")
        tk.Label(head, text="   cipher machine + morse messenger", bg=BG, fg=DIM,
                 font=("Consolas", 11)).pack(side="left", pady=(10, 0))
        modes = tk.Frame(head, bg=BG)
        modes.pack(side="right")
        for label, val in (("CLASSIC  A-Z", "classic"), ("EXTENDED  A-Z 0-9 + symbols", "extended")):
            tk.Radiobutton(modes, text=label, value=val, variable=self.mode,
                           command=self.apply_mode, bg=PANEL, fg=DIM,
                           selectcolor="#17405a", activebackground=EDGE,
                           activeforeground=CYAN, font=("Consolas", 9, "bold"),
                           indicatoron=0, padx=10, pady=5, relief="flat",
                           bd=0, cursor="hand2").pack(side="left", padx=2)

        self.status_lbl = tk.Label(self, text="", bg=PANEL2, fg=DIM, anchor="w",
                                   font=("Consolas", 9), padx=24, pady=5)
        self.status_lbl.pack(fill="x", side="bottom")

        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=0, pady=(6, 0))
        main = tk.Frame(self.nb, bg=BG)
        self.nb.add(main, text="  CIPHER  ")
        self.msg_tab = MessengerTab(self.nb, self)
        self.nb.add(self.msg_tab, text="  MESSENGER  ")

        # machine panel
        machine = tk.Frame(main, bg=PANEL, highlightthickness=1,
                           highlightbackground=EDGE)
        machine.pack(fill="x", padx=24, pady=8)

        rotors = tk.Frame(machine, bg=PANEL)
        rotors.pack(side="left", padx=24, pady=16)
        self.rotors = []
        for title in ("LEFT", "MIDDLE", "RIGHT"):
            r = RotorUI(rotors, title, self.on_setting_change)
            r.pack(side="left", padx=14)
            self.rotors.append(r)

        side = tk.Frame(machine, bg=PANEL)
        side.pack(side="left", fill="both", expand=True, padx=(10, 24), pady=16)

        tk.Label(side, text="REFLECTOR", bg=PANEL, fg=DIM,
                 font=("Consolas", 9, "bold")).pack(anchor="w")
        self.refl_combo = ttk.Combobox(side, textvariable=self.refl_var,
                                       state="readonly", width=6)
        self.refl_combo.pack(anchor="w", pady=(2, 12))
        self.refl_var.trace_add("write", lambda *_: self.on_setting_change())

        self.plug_label = tk.Label(side, text="PLUGBOARD  (pairs, e.g. AB CD EF)",
                                   bg=PANEL, fg=DIM, font=("Consolas", 9, "bold"))
        self.plug_label.pack(anchor="w")
        self.plug_entry = tk.Entry(side, textvariable=self.plug_var, bg=PANEL2,
                                   fg=AMBER, insertbackground=CYAN, relief="flat",
                                   font=("Consolas", 13), highlightthickness=1,
                                   highlightbackground=EDGE,
                                   highlightcolor=CYAN)
        self.plug_entry.pack(fill="x", pady=(2, 12), ipady=5)
        self.plug_var.trace_add("write", lambda *_: self.on_setting_change())

        tk.Label(side, text="KEY CODE  (share this to decrypt)", bg=PANEL,
                 fg=DIM, font=("Consolas", 9, "bold")).pack(anchor="w")
        self.key_entry = tk.Entry(side, textvariable=self.key_var, bg=PANEL2,
                                  fg=CYAN, insertbackground=CYAN, relief="flat",
                                  font=("Consolas", 10), highlightthickness=1,
                                  highlightbackground=EDGE, highlightcolor=CYAN)
        self.key_entry.pack(fill="x", pady=(2, 6), ipady=5)

        row = tk.Frame(side, bg=PANEL)
        row.pack(anchor="w", pady=(4, 0))
        self.button(row, "\u2684  RANDOMIZE", self.randomize, True).pack(side="left", padx=(0, 6))
        self.button(row, "Copy key", self.copy_key).pack(side="left", padx=3)
        self.button(row, "Load key", self.load_key).pack(side="left", padx=3)

        # lampboard
        self.lamp_canvas = tk.Canvas(main, height=170, bg=BG,
                                     highlightthickness=0)
        self.lamp_canvas.pack(fill="x", padx=24, pady=(4, 0))
        self._build_lamps()

        # io
        io = tk.Frame(main, bg=BG)
        io.pack(fill="both", expand=True, padx=24, pady=(6, 0))
        io.columnconfigure(0, weight=1, uniform="io")
        io.columnconfigure(1, weight=1, uniform="io")
        io.rowconfigure(1, weight=1)

        tk.Label(io, text="INPUT", bg=BG, fg=DIM,
                 font=("Consolas", 9, "bold")).grid(row=0, column=0, sticky="w")
        tk.Label(io, text="OUTPUT", bg=BG, fg=DIM,
                 font=("Consolas", 9, "bold")).grid(row=0, column=1, sticky="w", padx=(10, 0))
        self.inp = self._textbox(io, TEXT)
        self.inp.grid(row=1, column=0, sticky="nsew")
        self.out = self._textbox(io, AMBER)
        self.out.grid(row=1, column=1, sticky="nsew", padx=(10, 0))
        self.inp.bind("<KeyRelease>", lambda e: self.live.get() and self.process())

        bar = tk.Frame(main, bg=BG)
        bar.pack(fill="x", padx=24, pady=10)
        self.button(bar, "ENCRYPT / DECRYPT", self.process, True).pack(side="left")
        self.button(bar, "\u21c4 Output \u2192 Input", self.swap).pack(side="left", padx=6)
        self.button(bar, "Copy output", self.copy_out).pack(side="left")
        self.button(bar, "Clear", self.clear).pack(side="left", padx=6)
        tk.Checkbutton(bar, text="Live", variable=self.live, bg=BG, fg=TEXT,
                       selectcolor=PANEL2, activebackground=BG,
                       activeforeground=CYAN, font=("Consolas", 10),
                       cursor="hand2").pack(side="left", padx=10)
        self.end_lbl = tk.Label(bar, text="", bg=BG, fg=DIM, font=("Consolas", 10))
        self.end_lbl.pack(side="right")

    def _textbox(self, parent, fg):
        return tk.Text(parent, bg=PANEL2, fg=fg, insertbackground=CYAN,
                       relief="flat", font=("Consolas", 13), wrap="word",
                       height=8, padx=12, pady=10, highlightthickness=1,
                       highlightbackground=EDGE, highlightcolor=CYAN,
                       selectbackground="#1d3b53", selectforeground=TEXT)

    def _build_lamps(self):
        c = self.lamp_canvas
        rows = ["QWERTYUIOP", "ASDFGHJKL", "ZXCVBNM"]
        step, r = 56, 19
        cx0 = 520
        for ri, row in enumerate(rows):
            y = 30 + ri * 50
            x0 = cx0 - (len(row) - 1) * step / 2
            for i, ch in enumerate(row):
                x = x0 + i * step
                glow = c.create_oval(x - r - 8, y - r - 8, x + r + 8, y + r + 8,
                                     fill="#3a2a10", outline="", state="hidden")
                lamp = c.create_oval(x - r, y - r, x + r, y + r, fill=PANEL,
                                     outline=EDGE, width=2)
                txt = c.create_text(x, y, text=ch, fill=DIM,
                                    font=("Consolas", 14, "bold"))
                self.lamps[ch] = (glow, lamp, txt)

    def flash(self, ch):
        if ch not in self.lamps:
            return
        for k, (g, l, t) in self.lamps.items():
            self.lamp_canvas.itemconfig(g, state="hidden")
            self.lamp_canvas.itemconfig(l, fill=PANEL, outline=EDGE)
            self.lamp_canvas.itemconfig(t, fill=DIM)
        g, l, t = self.lamps[ch]
        self.lamp_canvas.itemconfig(g, state="normal")
        self.lamp_canvas.itemconfig(l, fill=AMBER, outline="#ffd9a0")
        self.lamp_canvas.itemconfig(t, fill=BG)

    # ---- state
    @property
    def profile(self):
        return PROFILES[self.mode.get()]

    def apply_mode(self):
        if not self.ready:
            return
        p = self.profile
        names = list(p["rotors"])
        self.ready = False
        for i, r in enumerate(self.rotors):
            r.configure_alphabet(p["alphabet"], names)
            r.name.set(names[i])
        self.refl_combo["values"] = list(p["reflectors"])
        self.refl_var.set("B")
        self.plug_var.set("")
        self.plug_label.config(
            text="PLUGBOARD  (pairs, e.g. AB CD EF"
                 + (" - letters & digits)" if self.mode.get() == "extended" else ")"))
        self.ready = True
        self.on_setting_change()

    def parse_plugs(self, s):
        allowed = self.profile["plugchars"]
        used, pairs = set(), []
        for t in s.upper().split():
            if len(t) != 2 or t[0] == t[1]:
                raise ValueError(f"Bad plug pair '{t}' (needs two different symbols)")
            for ch in t:
                if ch not in allowed:
                    raise ValueError(f"'{ch}' can't be plugged in this mode")
                if ch in used:
                    raise ValueError(f"'{ch}' is plugged more than once")
                used.add(ch)
            pairs.append(t)
        if len(pairs) > 13:
            raise ValueError("Max 13 plug pairs")
        return pairs

    def collect(self):
        order = [r.name.get() for r in self.rotors]
        if len(set(order)) < 3:
            raise ValueError("Pick three different rotors")
        return {
            "m": self.mode.get(),
            "o": order,
            "p": [r.pos.get() for r in self.rotors],
            "r": [r.ring_index() for r in self.rotors],
            "f": self.refl_var.get(),
            "s": self.parse_plugs(self.plug_var.get()),
        }

    def apply_cfg(self, cfg):
        if cfg["m"] != self.mode.get():
            self.mode.set(cfg["m"])
            self.apply_mode()
        self.ready = False
        for r, name, pos, ring in zip(self.rotors, cfg["o"], cfg["p"], cfg["r"]):
            r.name.set(name)
            r.pos.set(pos)
            r.set_ring(ring)
        self.refl_var.set(cfg["f"])
        self.plug_var.set(" ".join(cfg["s"]))
        self.ready = True
        self.on_setting_change()

    def randomize(self):
        p = self.profile
        n = len(p["alphabet"])
        names = list(p["rotors"])
        pc = list(p["plugchars"])
        self.rng.shuffle(pc)
        npairs = self.rng.randint(6, 10)
        pairs = ["".join(pc[i * 2:i * 2 + 2]) for i in range(npairs)]
        cfg = {
            "m": self.mode.get(),
            "o": self.rng.sample(names, 3),
            "p": [self.rng.randrange(n) for _ in range(3)],
            "r": [self.rng.randrange(n) for _ in range(3)],
            "f": self.rng.choice(list(p["reflectors"])),
            "s": pairs,
        }
        self.apply_cfg(cfg)
        self.status("New random machine setup generated. Copy the key code to decrypt later.")

    # ---- events
    def on_setting_change(self):
        if not self.ready or self._pending:
            return
        self._pending = True
        self.after_idle(self._settings_changed)

    def _settings_changed(self):
        self._pending = False
        try:
            cfg = self.collect()
        except ValueError as e:
            self.status(str(e), err=True)
            return
        self.key_var.set(encode_key(cfg))
        self.status("Settings OK.")
        if self.live.get():
            self.process()

    def process(self):
        try:
            cfg = self.collect()
        except ValueError as e:
            self.status(str(e), err=True)
            return
        p = self.profile
        m = Enigma(p, cfg["o"], cfg["p"], cfg["r"], cfg["f"], cfg["s"])
        result = m.process(self.inp.get("1.0", "end-1c"))
        self.out.delete("1.0", "end")
        self.out.insert("1.0", result)
        end = " ".join(disp(p["alphabet"][i]) for i in m.pos)
        self.end_lbl.config(text=f"rotors ended at  {end}")
        if m.last_out:
            self.flash(m.last_out)

    def load_key(self):
        try:
            self.apply_cfg(decode_key(self.key_var.get()))
            self.status("Key loaded.")
        except (ValueError, KeyError, TypeError, IndexError) as e:
            self.status(f"Couldn't load key: {e}", err=True)

    def copy_key(self):
        self.clipboard_clear()
        self.clipboard_append(self.key_var.get())
        self.status("Key code copied to clipboard.")

    def copy_out(self):
        self.clipboard_clear()
        self.clipboard_append(self.out.get("1.0", "end-1c"))
        self.status("Output copied to clipboard.")

    def swap(self):
        txt = self.out.get("1.0", "end-1c")
        self.inp.delete("1.0", "end")
        self.inp.insert("1.0", txt)
        self.process()

    def clear(self):
        self.inp.delete("1.0", "end")
        self.out.delete("1.0", "end")
        self.end_lbl.config(text="")

    def status(self, msg, err=False):
        self.status_lbl.config(text=msg, fg=RED if err else DIM)


if __name__ == "__main__":
    App().mainloop()