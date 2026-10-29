#!/usr/bin/env python3
"""
CatChip-8 1.0 - CHIP-8 emulator with an mGBA-style blue GUI
Copyright (c) 2026 A.C Holdings / Team Flames. All rights reserved.

Single file, standard library only (tkinter). Runs on Python 3.8+ (incl. 3.15).

Menus : File (Load ROM / Exit) | Settings | Play | Game | Help (About / Copyright)
Keys  : 1 2 3 4 / Q W E R / A S D F / Z X C V  ->  CHIP-8 keypad
        Ctrl+O load ROM, F5 play/pause, F6 single step, Ctrl+R reset
Usage : python catchip8.py [rom.ch8]
"""

import json
import os
import random
import sys
import threading
import time

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox
except ImportError:  # core still importable for testing without Tk
    tk = None

try:
    import winsound  # Windows only
except ImportError:
    winsound = None

APP_NAME = "CatChip-8"
APP_VERSION = "1.0"
COPYRIGHT = "Copyright \u00a9 2026 A.C Holdings / Team Flames. All rights reserved."
SETTINGS_PATH = os.path.join(os.path.expanduser("~"), ".catchip8.json")

# ----------------------------------------------------------------------------
# Theme
# ----------------------------------------------------------------------------
BG = "#a8c8ff"            # blue hue window background
TEXT = "#001f9e"          # blue text
BTN_BG = "#000000"        # black buttons
BTN_FG = "#5aa9ff"
BTN_ACTIVE = "#0a0a3a"
VB6_GRAY = "#c0c0c0"      # classic VB6 menu strip
VB6_NAVY = "#000080"

PALETTES = {
    "Blue Hue":       ("#00061a", "#7fc4ff"),
    "Green Phosphor": ("#001a00", "#33ff66"),
    "Amber":          ("#1a0f00", "#ffb000"),
    "Mono":           ("#000000", "#ffffff"),
}

QUIRK_PRESETS = {
    "Modern": dict(shift_vx=True, mem_inc=False, jump_vx=False, vf_reset=False, clip=True),
    "Original CHIP-8": dict(shift_vx=False, mem_inc=True, jump_vx=False, vf_reset=True, clip=True),
}
QUIRK_LABELS = {
    "shift_vx": "Shift ops use VX (not VY)",
    "mem_inc": "Load/Store increment I",
    "jump_vx": "BXNN jumps with VX (not V0)",
    "vf_reset": "AND/OR/XOR reset VF",
    "clip": "Clip sprites at screen edge",
}

KEYMAP = {
    "1": 0x1, "2": 0x2, "3": 0x3, "4": 0xC,
    "q": 0x4, "w": 0x5, "e": 0x6, "r": 0xD,
    "a": 0x7, "s": 0x8, "d": 0x9, "f": 0xE,
    "z": 0xA, "x": 0x0, "c": 0xB, "v": 0xF,
}

FONT = [
    0xF0, 0x90, 0x90, 0x90, 0xF0, 0x20, 0x60, 0x20, 0x20, 0x70,
    0xF0, 0x10, 0xF0, 0x80, 0xF0, 0xF0, 0x10, 0xF0, 0x10, 0xF0,
    0x90, 0x90, 0xF0, 0x10, 0x10, 0xF0, 0x80, 0xF0, 0x10, 0xF0,
    0xF0, 0x80, 0xF0, 0x90, 0xF0, 0xF0, 0x10, 0x20, 0x40, 0x40,
    0xF0, 0x90, 0xF0, 0x90, 0xF0, 0xF0, 0x90, 0xF0, 0x10, 0xF0,
    0xF0, 0x90, 0xF0, 0x90, 0x90, 0xE0, 0x90, 0xE0, 0x90, 0xE0,
    0xF0, 0x80, 0x80, 0x80, 0xF0, 0xE0, 0x90, 0x90, 0x90, 0xE0,
    0xF0, 0x80, 0xF0, 0x80, 0xF0, 0xF0, 0x80, 0xF0, 0x80, 0x80,
]
FONT_BASE = 0x50

# Built-in demo: clears the screen and draws the digits 0-7 using the font.
DEMO_ROM = bytes.fromhex(
    "00E0" "6300" "6002" "6104" "F329" "D015"
    "7005" "7301" "3308" "1208" "1214"
)


# ----------------------------------------------------------------------------
# CHIP-8 core
# ----------------------------------------------------------------------------
class Chip8:
    W = 64
    H = 32

    def __init__(self):
        self.quirks = dict(QUIRK_PRESETS["Modern"])
        self.keys = [False] * 16
        self.rom = b""
        self.reset()

    def reset(self):
        self.mem = bytearray(4096)
        self.mem[FONT_BASE:FONT_BASE + len(FONT)] = bytes(FONT)
        if self.rom:
            self.mem[0x200:0x200 + len(self.rom)] = self.rom
        self.V = [0] * 16
        self.I = 0
        self.pc = 0x200
        self.stack = []
        self.DT = 0
        self.ST = 0
        self.gfx = bytearray(self.W * self.H)
        self.key_event = None
        self.draw_flag = True
        self.halted = False
        self.error = ""
        self.cycles = 0

    def load_rom(self, data):
        if not data:
            raise ValueError("ROM is empty.")
        if len(data) > 4096 - 0x200:
            raise ValueError("ROM is too large (max %d bytes)." % (4096 - 0x200))
        self.rom = bytes(data)
        self.reset()

    def tick_timers(self):
        if self.DT:
            self.DT -= 1
        if self.ST:
            self.ST -= 1

    def _fail(self, msg):
        self.halted = True
        self.error = msg

    def step(self):
        if self.halted:
            return
        mem, V, q = self.mem, self.V, self.quirks
        pc = self.pc
        op = (mem[pc] << 8) | mem[(pc + 1) & 0xFFF]
        self.pc = (pc + 2) & 0xFFF
        self.cycles += 1

        n1 = op >> 12
        x = (op >> 8) & 0xF
        y = (op >> 4) & 0xF
        n = op & 0xF
        nn = op & 0xFF
        nnn = op & 0xFFF

        if n1 == 0x0:
            if op == 0x00E0:
                self.gfx = bytearray(self.W * self.H)
                self.draw_flag = True
            elif op == 0x00EE:
                if not self.stack:
                    return self._fail("Stack underflow at %03X" % pc)
                self.pc = self.stack.pop()
            else:
                pass  # 0NNN (SYS) is ignored
        elif n1 == 0x1:
            self.pc = nnn
        elif n1 == 0x2:
            if len(self.stack) >= 16:
                return self._fail("Stack overflow at %03X" % pc)
            self.stack.append(self.pc)
            self.pc = nnn
        elif n1 == 0x3:
            if V[x] == nn:
                self.pc = (self.pc + 2) & 0xFFF
        elif n1 == 0x4:
            if V[x] != nn:
                self.pc = (self.pc + 2) & 0xFFF
        elif n1 == 0x5:
            if n != 0:
                return self._fail("Unknown opcode %04X at %03X" % (op, pc))
            if V[x] == V[y]:
                self.pc = (self.pc + 2) & 0xFFF
        elif n1 == 0x6:
            V[x] = nn
        elif n1 == 0x7:
            V[x] = (V[x] + nn) & 0xFF
        elif n1 == 0x8:
            if n == 0x0:
                V[x] = V[y]
            elif n == 0x1:
                V[x] |= V[y]
                if q["vf_reset"]:
                    V[0xF] = 0
            elif n == 0x2:
                V[x] &= V[y]
                if q["vf_reset"]:
                    V[0xF] = 0
            elif n == 0x3:
                V[x] ^= V[y]
                if q["vf_reset"]:
                    V[0xF] = 0
            elif n == 0x4:
                s = V[x] + V[y]
                V[x] = s & 0xFF
                V[0xF] = 1 if s > 0xFF else 0
            elif n == 0x5:
                f = 1 if V[x] >= V[y] else 0
                V[x] = (V[x] - V[y]) & 0xFF
                V[0xF] = f
            elif n == 0x6:
                src = V[x] if q["shift_vx"] else V[y]
                f = src & 1
                V[x] = src >> 1
                V[0xF] = f
            elif n == 0x7:
                f = 1 if V[y] >= V[x] else 0
                V[x] = (V[y] - V[x]) & 0xFF
                V[0xF] = f
            elif n == 0xE:
                src = V[x] if q["shift_vx"] else V[y]
                f = (src >> 7) & 1
                V[x] = (src << 1) & 0xFF
                V[0xF] = f
            else:
                return self._fail("Unknown opcode %04X at %03X" % (op, pc))
        elif n1 == 0x9:
            if n != 0:
                return self._fail("Unknown opcode %04X at %03X" % (op, pc))
            if V[x] != V[y]:
                self.pc = (self.pc + 2) & 0xFFF
        elif n1 == 0xA:
            self.I = nnn
        elif n1 == 0xB:
            off = V[x] if q["jump_vx"] else V[0]
            self.pc = (nnn + off) & 0xFFF
        elif n1 == 0xC:
            V[x] = random.getrandbits(8) & nn
        elif n1 == 0xD:
            self._draw(V[x], V[y], n)
        elif n1 == 0xE:
            if nn == 0x9E:
                if self.keys[V[x] & 0xF]:
                    self.pc = (self.pc + 2) & 0xFFF
            elif nn == 0xA1:
                if not self.keys[V[x] & 0xF]:
                    self.pc = (self.pc + 2) & 0xFFF
            else:
                return self._fail("Unknown opcode %04X at %03X" % (op, pc))
        elif n1 == 0xF:
            if nn == 0x07:
                V[x] = self.DT
            elif nn == 0x0A:
                if self.key_event is None:
                    self.pc = (self.pc - 2) & 0xFFF  # keep waiting
                else:
                    V[x] = self.key_event
                    self.key_event = None
            elif nn == 0x15:
                self.DT = V[x]
            elif nn == 0x18:
                self.ST = V[x]
            elif nn == 0x1E:
                self.I = (self.I + V[x]) & 0xFFF
            elif nn == 0x29:
                self.I = FONT_BASE + (V[x] & 0xF) * 5
            elif nn == 0x33:
                v = V[x]
                mem[self.I & 0xFFF] = v // 100
                mem[(self.I + 1) & 0xFFF] = (v // 10) % 10
                mem[(self.I + 2) & 0xFFF] = v % 10
            elif nn == 0x55:
                for i in range(x + 1):
                    mem[(self.I + i) & 0xFFF] = V[i]
                if q["mem_inc"]:
                    self.I = (self.I + x + 1) & 0xFFF
            elif nn == 0x65:
                for i in range(x + 1):
                    V[i] = mem[(self.I + i) & 0xFFF]
                if q["mem_inc"]:
                    self.I = (self.I + x + 1) & 0xFFF
            else:
                return self._fail("Unknown opcode %04X at %03X" % (op, pc))

    def _draw(self, vx, vy, n):
        W, H = self.W, self.H
        gfx, mem, V = self.gfx, self.mem, self.V
        clip = self.quirks["clip"]
        x0 = vx % W
        y0 = vy % H
        V[0xF] = 0
        for row in range(n):
            py = y0 + row
            if py >= H:
                if clip:
                    break
                py %= H
            byte = mem[(self.I + row) & 0xFFF]
            for col in range(8):
                if not (byte & (0x80 >> col)):
                    continue
                px = x0 + col
                if px >= W:
                    if clip:
                        break
                    px %= W
                idx = py * W + px
                if gfx[idx]:
                    V[0xF] = 1
                gfx[idx] ^= 1
        self.draw_flag = True

    # -- save states --------------------------------------------------------
    def get_state(self):
        return {
            "mem": self.mem.hex(), "V": list(self.V), "I": self.I, "pc": self.pc,
            "stack": list(self.stack), "DT": self.DT, "ST": self.ST,
            "gfx": self.gfx.hex(), "quirks": dict(self.quirks),
        }

    def set_state(self, s):
        mem = bytearray.fromhex(s["mem"])
        gfx = bytearray.fromhex(s["gfx"])
        if len(mem) != 4096 or len(gfx) != self.W * self.H or len(s["V"]) != 16:
            raise ValueError("Invalid save state.")
        self.mem, self.gfx = mem, gfx
        self.V = [int(v) & 0xFF for v in s["V"]]
        self.I = int(s["I"]) & 0xFFF
        self.pc = int(s["pc"]) & 0xFFF
        self.stack = [int(v) & 0xFFF for v in s["stack"]][:16]
        self.DT = int(s["DT"]) & 0xFF
        self.ST = int(s["ST"]) & 0xFF
        self.quirks.update(s.get("quirks", {}))
        self.key_event = None
        self.halted = False
        self.error = ""
        self.draw_flag = True


# ----------------------------------------------------------------------------
# GUI
# ----------------------------------------------------------------------------
FRAME_TIME = 1.0 / 60.0


class App:
    def __init__(self, root):
        self.root = root
        self.chip = Chip8()
        self.running = False
        self.rom_name = "(none)"
        self.rom_path = None
        self.cpf = 12                  # CPU cycles per 60 Hz frame (~720 Hz)
        self.scale = 10
        self.palette = "Blue Hue"
        self.sound = True
        self.preset = "Modern"
        self.beeping = False
        self.acc = 0.0
        self.last = time.perf_counter()
        self.release_jobs = {}
        self.photo = tk.PhotoImage(width=Chip8.W, height=Chip8.H)
        self.big = None
        self._load_settings()

        root.title("%s %s" % (APP_NAME, APP_VERSION))
        root.configure(bg=BG)
        root.resizable(True, True)
        root.minsize(640, 480)
        root.protocol("WM_DELETE_WINDOW", self.exit_app)

        self._build_menu()
        self._build_body()
        self._bind_keys()
        self.render()
        self._update_status()
        self._place_centered(800, 600)
        self.root.after(0, lambda: self._place_centered(800, 600))
        self.root.after(4, self._loop)

    def _place_centered(self, w=800, h=600):
        """Open as an 800×600 window centered on the primary screen."""
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x = max(0, (sw - w) // 2)
        y = max(0, (sh - h) // 2)
        self.root.geometry("%dx%d+%d+%d" % (w, h, x, y))

    # -- settings persistence ----------------------------------------------
    def _load_settings(self):
        try:
            with open(SETTINGS_PATH, "r", encoding="utf-8") as f:
                d = json.load(f)
            self.cpf = max(1, min(500, int(d.get("cpf", self.cpf))))
            self.scale = max(4, min(20, int(d.get("scale", self.scale))))
            if d.get("palette") in PALETTES:
                self.palette = d["palette"]
            self.sound = bool(d.get("sound", self.sound))
            if d.get("preset") in QUIRK_PRESETS:
                self.preset = d["preset"]
            q = d.get("quirks")
            self.chip.quirks = dict(QUIRK_PRESETS[self.preset])
            if isinstance(q, dict):
                for k in self.chip.quirks:
                    if k in q:
                        self.chip.quirks[k] = bool(q[k])
        except (OSError, ValueError, TypeError):
            pass

    def _save_settings(self):
        try:
            with open(SETTINGS_PATH, "w", encoding="utf-8") as f:
                json.dump({
                    "cpf": self.cpf, "scale": self.scale, "palette": self.palette,
                    "sound": self.sound, "preset": self.preset,
                    "quirks": self.chip.quirks,
                }, f, indent=2)
        except OSError:
            pass

    # -- widgets -------------------------------------------------------------
    def _btn(self, parent, text, cmd, width=10):
        return tk.Button(parent, text=text, command=cmd, width=width, bg=BTN_BG,
                         fg=BTN_FG, activebackground=BTN_ACTIVE, activeforeground="#ffffff",
                         relief="raised", bd=2, highlightthickness=0, takefocus=0)

    def _build_menu(self):
        bar = tk.Frame(self.root, bg=VB6_GRAY, bd=1, relief="raised")
        bar.pack(side="top", fill="x")

        def menu(label, items):
            mb = tk.Menubutton(bar, text=label, bg=VB6_GRAY, fg="#000000",
                               activebackground=VB6_NAVY, activeforeground="#ffffff",
                               relief="flat", bd=0, padx=8, pady=2, takefocus=0)
            m = tk.Menu(mb, tearoff=0, bg=VB6_GRAY, fg="#000000",
                        activebackground=VB6_NAVY, activeforeground="#ffffff", bd=1)
            for it in items:
                if it is None:
                    m.add_separator()
                else:
                    m.add_command(label=it[0], command=it[1],
                                  accelerator=it[2] if len(it) > 2 else None)
            mb.configure(menu=m)
            mb.pack(side="left")
            return m

        menu("File", [("Load ROM...", self.load_rom_dialog, "Ctrl+O"), None,
                      ("Exit", self.exit_app)])
        menu("Settings", [("Settings...", self.settings_dialog)])
        self.play_menu = menu("Play", [("Play / Pause", self.toggle_play, "F5"),
                                       ("Step", self.step_once, "F6"),
                                       ("Reset", self.reset, "Ctrl+R")])
        menu("Game", [("Load Demo ROM", self.load_demo), None,
                      ("Save State...", self.save_state),
                      ("Load State...", self.load_state), None,
                      ("Save Screenshot...", self.screenshot)])
        menu("Help", [("About", self.about), ("Copyright", self.copyright_info)])

    def _build_body(self):
        frame = tk.Frame(self.root, bg=BG, padx=8, pady=8)
        frame.pack(fill="both", expand=True)
        self.screen = tk.Label(frame, bg="#000000", bd=3, relief="sunken")
        self.screen.pack(expand=True)

        row = tk.Frame(frame, bg=BG)
        row.pack(fill="x", pady=(8, 0), side="bottom")
        self._btn(row, "Load ROM", self.load_rom_dialog).pack(side="left", padx=2)
        self.play_btn = self._btn(row, "Play", self.toggle_play)
        self.play_btn.pack(side="left", padx=2)
        self._btn(row, "Reset", self.reset).pack(side="left", padx=2)
        self._btn(row, "Settings", self.settings_dialog).pack(side="left", padx=2)
        self._btn(row, "Exit", self.exit_app).pack(side="right", padx=2)

        self.status = tk.Label(self.root, text="", anchor="w", bg=BG, fg=TEXT,
                               bd=1, relief="sunken", padx=6, pady=2)
        self.status.pack(side="bottom", fill="x")

    def _bind_keys(self):
        r = self.root
        r.bind("<KeyPress>", self._key_down)
        r.bind("<KeyRelease>", self._key_up)
        r.bind("<Control-o>", lambda e: self.load_rom_dialog())
        r.bind("<Control-r>", lambda e: self.reset())
        r.bind("<F5>", lambda e: self.toggle_play())
        r.bind("<F6>", lambda e: self.step_once())
        r.focus_set()

    # -- input -----------------------------------------------------------------
    def _key_down(self, e):
        k = KEYMAP.get(e.keysym.lower())
        if k is None:
            return
        job = self.release_jobs.pop(k, None)
        if job:
            self.root.after_cancel(job)       # swallow X11 auto-repeat
        if not self.chip.keys[k]:
            self.chip.key_event = k
        self.chip.keys[k] = True

    def _key_up(self, e):
        k = KEYMAP.get(e.keysym.lower())
        if k is None:
            return

        def release(k=k):
            self.release_jobs.pop(k, None)
            self.chip.keys[k] = False
        self.release_jobs[k] = self.root.after(25, release)

    # -- emulation control -----------------------------------------------------
    def load_rom_dialog(self):
        path = filedialog.askopenfilename(
            title="Load ROM",
            filetypes=[("CHIP-8 ROMs", "*.ch8 *.c8 *.rom *.bin"), ("All files", "*.*")])
        if path:
            self.load_rom_path(path)

    def load_rom_path(self, path):
        try:
            with open(path, "rb") as f:
                data = f.read()
            self.chip.load_rom(data)
        except (OSError, ValueError) as ex:
            messagebox.showerror("Load ROM", str(ex), parent=self.root)
            return
        self.rom_path = path
        self.rom_name = os.path.basename(path)
        self.acc = 0.0
        self._set_running(True)

    def load_demo(self):
        self.chip.load_rom(DEMO_ROM)
        self.rom_path = None
        self.rom_name = "Built-in demo"
        self.acc = 0.0
        self._set_running(True)

    def reset(self):
        self.chip.reset()
        self.acc = 0.0
        self.beeping = False
        self._update_status()

    def toggle_play(self):
        if not self.chip.rom:
            self.load_rom_dialog()
            return
        if self.chip.halted:
            self.chip.halted = False
            self.chip.error = ""
        self._set_running(not self.running)

    def step_once(self):
        self._set_running(False)
        self.chip.step()
        self.render()
        self._update_status()

    def _set_running(self, state):
        self.running = state
        self.play_btn.config(text="Pause" if state else "Play")
        self.last = time.perf_counter()
        self._update_status()

    # -- main loop -------------------------------------------------------------
    def _loop(self):
        now = time.perf_counter()
        dt = now - self.last
        self.last = now
        chip = self.chip
        if self.running and not chip.halted:
            self.acc = min(self.acc + dt, 0.25)
            while self.acc >= FRAME_TIME and not chip.halted:
                self.acc -= FRAME_TIME
                for _ in range(self.cpf):
                    chip.step()
                    if chip.halted:
                        break
                chip.tick_timers()
                self._sound()
            if chip.halted:
                self._set_running(False)
                self.play_btn.config(text="Play")
                messagebox.showwarning("Emulation stopped", chip.error, parent=self.root)
        if chip.draw_flag:
            self.render()
        if int(now * 4) != getattr(self, "_last_status", None):
            self._last_status = int(now * 4)
            self._update_status()
        self.root.after(4, self._loop)

    def _sound(self):
        if self.chip.ST > 0 and self.sound:
            if not self.beeping:
                self.beeping = True
                if winsound:
                    threading.Thread(target=winsound.Beep, args=(880, 80), daemon=True).start()
                else:
                    self.root.bell()
        else:
            self.beeping = False

    def render(self):
        off, on = PALETTES[self.palette]
        pix = (off, on)
        g = self.chip.gfx
        W = Chip8.W
        rows = []
        for y in range(Chip8.H):
            rows.append("{" + " ".join(pix[p] for p in g[y * W:(y + 1) * W]) + "}")
        self.photo.put(" ".join(rows))
        self.big = self.photo.zoom(self.scale, self.scale)
        self.screen.config(image=self.big)
        self.chip.draw_flag = False

    def _update_status(self):
        if self.chip.halted:
            state = "Halted"
        elif self.running:
            state = "Running"
        else:
            state = "Paused"
        self.status.config(text="ROM: %s   |   %s   |   %d cycles/frame (~%d Hz)   |   PC=%03X"
                           % (self.rom_name, state, self.cpf, self.cpf * 60, self.chip.pc))

    # -- save state / screenshot ------------------------------------------------
    def save_state(self):
        if not self.chip.rom:
            messagebox.showinfo("Save State", "Load a ROM first.", parent=self.root)
            return
        path = filedialog.asksaveasfilename(title="Save State", defaultextension=".c8state",
                                            filetypes=[("CatChip-8 state", "*.c8state")])
        if path:
            try:
                with open(path, "w", encoding="utf-8") as f:
                    json.dump(self.chip.get_state(), f)
            except OSError as ex:
                messagebox.showerror("Save State", str(ex), parent=self.root)

    def load_state(self):
        path = filedialog.askopenfilename(title="Load State",
                                          filetypes=[("CatChip-8 state", "*.c8state")])
        if path:
            try:
                with open(path, "r", encoding="utf-8") as f:
                    self.chip.set_state(json.load(f))
                self._set_running(True)
            except (OSError, ValueError, KeyError, TypeError) as ex:
                messagebox.showerror("Load State", "Could not load state:\n%s" % ex,
                                     parent=self.root)

    def screenshot(self):
        path = filedialog.asksaveasfilename(title="Save Screenshot", defaultextension=".png",
                                            filetypes=[("PNG image", "*.png")])
        if path and self.big is not None:
            try:
                self.big.write(path, format="png")
            except (tk.TclError, OSError) as ex:
                messagebox.showerror("Screenshot", str(ex), parent=self.root)

    # -- dialogs ----------------------------------------------------------------
    def settings_dialog(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("Settings")
        dlg.configure(bg=BG, padx=12, pady=10)
        dlg.resizable(False, False)
        dlg.transient(self.root)

        def label(parent, text, **kw):
            return tk.Label(parent, text=text, bg=BG, fg=TEXT, anchor="w", **kw)

        def option(parent, var, values, cmd=None):
            om = tk.OptionMenu(parent, var, *values, command=cmd)
            om.config(bg=BTN_BG, fg=BTN_FG, activebackground=BTN_ACTIVE,
                      activeforeground="#ffffff", highlightthickness=0, width=16)
            om["menu"].config(bg=BTN_BG, fg=BTN_FG, activebackground=VB6_NAVY,
                              activeforeground="#ffffff")
            return om

        cpf_var = tk.IntVar(value=self.cpf)
        scale_var = tk.IntVar(value=self.scale)
        pal_var = tk.StringVar(value=self.palette)
        snd_var = tk.BooleanVar(value=self.sound)
        preset_var = tk.StringVar(value=self.preset)
        qvars = {k: tk.BooleanVar(value=self.chip.quirks[k]) for k in QUIRK_LABELS}

        grid = tk.Frame(dlg, bg=BG)
        grid.pack(fill="x")
        label(grid, "CPU cycles per frame (60 fps):").grid(row=0, column=0, sticky="w", pady=3)
        tk.Spinbox(grid, from_=1, to=500, width=6, textvariable=cpf_var, bg="#000000",
                   fg=BTN_FG, buttonbackground="#000000", insertbackground=BTN_FG
                   ).grid(row=0, column=1, sticky="w", padx=6)
        label(grid, "Screen scale:").grid(row=1, column=0, sticky="w", pady=3)
        tk.Scale(grid, from_=4, to=20, orient="horizontal", variable=scale_var, length=140,
                 bg=BG, fg=TEXT, troughcolor="#000000", highlightthickness=0
                 ).grid(row=1, column=1, sticky="w", padx=6)
        label(grid, "Color scheme:").grid(row=2, column=0, sticky="w", pady=3)
        option(grid, pal_var, list(PALETTES)).grid(row=2, column=1, sticky="w", padx=6)
        label(grid, "Compatibility preset:").grid(row=3, column=0, sticky="w", pady=3)

        def apply_preset(name):
            for k, v in QUIRK_PRESETS[name].items():
                qvars[k].set(v)
        option(grid, preset_var, list(QUIRK_PRESETS), apply_preset).grid(
            row=3, column=1, sticky="w", padx=6)

        box = tk.LabelFrame(dlg, text=" Quirks ", bg=BG, fg=TEXT, padx=8, pady=4)
        box.pack(fill="x", pady=8)
        for k, text in QUIRK_LABELS.items():
            tk.Checkbutton(box, text=text, variable=qvars[k], bg=BG, fg=TEXT,
                           activebackground=BG, activeforeground=TEXT, selectcolor="#ffffff",
                           anchor="w").pack(fill="x")
        tk.Checkbutton(dlg, text="Sound (beep)", variable=snd_var, bg=BG, fg=TEXT,
                       activebackground=BG, activeforeground=TEXT, selectcolor="#ffffff",
                       anchor="w").pack(fill="x")

        def ok():
            try:
                self.cpf = max(1, min(500, int(cpf_var.get())))
            except (tk.TclError, ValueError):
                pass
            self.scale = int(scale_var.get())
            self.palette = pal_var.get()
            self.sound = bool(snd_var.get())
            self.preset = preset_var.get()
            for k, v in qvars.items():
                self.chip.quirks[k] = bool(v.get())
            self._save_settings()
            self.render()
            self._update_status()
            dlg.destroy()

        btns = tk.Frame(dlg, bg=BG)
        btns.pack(fill="x", pady=(10, 0))
        self._btn(btns, "OK", ok, 8).pack(side="right", padx=2)
        self._btn(btns, "Cancel", dlg.destroy, 8).pack(side="right", padx=2)
        dlg.grab_set()

    def about(self):
        messagebox.showinfo(
            "About %s" % APP_NAME,
            "%s %s\nCHIP-8 emulator with an mGBA-style GUI.\n\n"
            "Keypad:\n 1 2 3 4\n Q W E R\n A S D F\n Z X C V\n\n%s"
            % (APP_NAME, APP_VERSION, COPYRIGHT), parent=self.root)

    def copyright_info(self):
        messagebox.showinfo("Copyright", COPYRIGHT, parent=self.root)

    def exit_app(self):
        self._save_settings()
        self.root.destroy()


def main():
    if tk is None:
        sys.exit("tkinter is not installed. Install it (e.g. 'sudo apt install python3-tk').")
    root = tk.Tk()
    app = App(root)
    if len(sys.argv) > 1 and os.path.isfile(sys.argv[1]):
        app.load_rom_path(sys.argv[1])
    else:
        app.load_demo()
    root.mainloop()


if __name__ == "__main__":
    main()
