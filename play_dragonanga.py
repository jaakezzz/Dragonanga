"""Dragonanga engine tester (Fairy-Stockfish).

Controls
  * Left click            select / move a piece (also clears drawn arrows)
  * Right click + drag    draw an arrow (lichess style); right click a square for a circle.
                          Same arrow again removes it.
                          Colours: none = green, Shift = red, Ctrl = orange, Alt = purple
  * Flip Board            swap which side is at the bottom (New Game as Black flips automatically)
  * Show best move        runs the engine in the background on your turn and draws its best
                          move as a blue arrow (uses one CPU core while it is on)
  * Eval is always from White's point of view: + = White ahead, - = Black ahead
"""
import math
import os
import re
import subprocess
import threading
import cairo
import gi

gi.require_version("Gtk", "3.0")
from gi.repository import Gtk, Gdk, GLib

# ---------------------------------------------------------------------------
# Piece display.  Maps the ENGINE's letter (the ones used in variant.cpp, in the
# FEN and in UCI promotion suffixes) to (symbol drawn on the piece, full name).
# Only what is drawn is translated; nothing sent to or read from the engine is.
# ---------------------------------------------------------------------------
PIECE_DISPLAY = {
    "P": ("S", "Soldier"),
    "I": ("G", "Guard"),
    "E": ("E", "Elephant"),
    "H": ("H", "Horse"),
    "D": ("D", "Dragon"),
    "K": ("Q", "Queen Fairy"),  # engine KING type (royal), moves like a fers
    "C": ("K", "King"),         # engine COMMONER
    "F": ("F", "Fairy"),
    "M": ("M", "Minister"),
}


def display_piece(letter):
    """Engine letter (any case) -> (symbol, name) for drawing."""
    return PIECE_DISPLAY.get(letter.upper(), (letter.upper(), ""))


# Arrow / circle colours (r, g, b)
BRUSHES = {
    "green": (0.08, 0.47, 0.11),
    "red": (0.74, 0.16, 0.16),
    "orange": (0.90, 0.56, 0.00),
    "purple": (0.55, 0.25, 0.75),
}
BEST_COLOR = (0.10, 0.42, 0.88)  # engine best-move arrow (blue)


# ---------------------------------------------------------------------------
# Pure helpers (no GTK needed)
# ---------------------------------------------------------------------------
def screen_to_sq(r, c, flipped):
    """Screen row/column (0,0 = top-left) -> square name such as 'e4'."""
    if flipped:
        r, c = 7 - r, 7 - c
    return f"{chr(ord('a') + c)}{8 - r}"


def sq_to_screen(name, flipped):
    """Square name -> screen (row, column)."""
    c = ord(name[0]) - ord("a")
    r = 8 - int(name[1])
    if flipped:
        r, c = 7 - r, 7 - c
    return r, c


def point_to_sq(x, y, size, flipped):
    """Pixel position -> square name, or None if outside the board."""
    sq_size = size / 8.0
    if sq_size <= 0 or x < 0 or y < 0:
        return None
    c = int(x // sq_size)
    r = int(y // sq_size)
    if not (0 <= r < 8 and 0 <= c < 8):
        return None
    return screen_to_sq(r, c, flipped)


def parse_info_line(line, stm):
    """Parse a UCI 'info' line.

    UCI scores are from the point of view of the side to move (stm), which is
    why they looked "always positive" when the engine played Black.  Returns a
    dict with the score converted to White's point of view, or None for lines
    that carry no usable score (or only a bound).
    """
    cp_m = re.search(r"\bscore\s+cp\s+(-?\d+)", line)
    mate_m = re.search(r"\bscore\s+mate\s+(-?\d+)", line)
    if not (cp_m or mate_m):
        return None
    if " lowerbound" in line or " upperbound" in line:
        return None
    sign = 1 if stm == "w" else -1
    if mate_m:
        score = f"#{int(mate_m.group(1)) * sign}"  # '#3' White mates in 3, '#-3' Black mates in 3
    else:
        score = f"{int(cp_m.group(1)) * sign / 100.0:+.2f}"
    depth_m = re.search(r"\bdepth\s+(\d+)", line)
    pv_m = re.search(r"\bpv\s+(.+)$", line)
    return {
        "depth": int(depth_m.group(1)) if depth_m else None,
        "score": score,
        "pv": pv_m.group(1).split() if pv_m else [],
    }


def format_eval(info):
    pv = " ".join(info["pv"])
    if len(pv) > 48:
        pv = pv[:48] + "..."
    depth = info["depth"] if info["depth"] is not None else "?"
    return f"Eval (White's view): {info['score']} | Depth: {depth} | Line: {pv}"


class Annotations:
    """Arrows and circles drawn with the right mouse button."""

    def __init__(self):
        self.arrows = []   # (from_sq, to_sq, brush)
        self.circles = []  # (sq, brush)
        self.drag_from = None
        self.drag_to = None
        self.drag_brush = "green"

    @staticmethod
    def _toggle(items, key, brush):
        for i, item in enumerate(items):
            if item[:-1] == key:
                if item[-1] == brush:
                    del items[i]            # same shape, same colour -> remove
                else:
                    items[i] = key + (brush,)  # same shape, new colour -> recolour
                return
        items.append(key + (brush,))

    def begin(self, sq, brush):
        self.drag_from, self.drag_to, self.drag_brush = sq, sq, brush

    def update(self, sq):
        if self.drag_from is not None:
            self.drag_to = sq

    def finish(self, sq):
        """Mouse released on `sq` (None = off the board, which cancels)."""
        start, brush = self.drag_from, self.drag_brush
        self.drag_from = self.drag_to = None
        if start is None or sq is None:
            return
        if sq == start:
            self._toggle(self.circles, (sq,), brush)
        else:
            self._toggle(self.arrows, (start, sq), brush)

    def clear(self):
        """Remove everything; returns True if something was removed."""
        changed = bool(self.arrows or self.circles)
        self.arrows, self.circles = [], []
        return changed


# ---------------------------------------------------------------------------
# Drawing (only needs a cairo context)
# ---------------------------------------------------------------------------
def _centre(name, flipped, sq):
    r, c = sq_to_screen(name, flipped)
    return (c + 0.5) * sq, (r + 0.5) * sq


def draw_arrow(cr, sq, frm, to, flipped, rgb, alpha=0.8):
    x1, y1 = _centre(frm, flipped, sq)
    x2, y2 = _centre(to, flipped, sq)
    dx, dy = x2 - x1, y2 - y1
    dist = math.hypot(dx, dy)
    if dist < 1e-6:
        return
    ux, uy = dx / dist, dy / dist
    px, py = -uy, ux
    sx, sy = x1 + ux * sq * 0.18, y1 + uy * sq * 0.18  # shaft start, just off the centre
    tx, ty = x2 - ux * sq * 0.12, y2 - uy * sq * 0.12  # tip, just short of the centre
    length = math.hypot(tx - sx, ty - sy)
    head_len = min(sq * 0.42, length * 0.8)
    head_half = sq * 0.26
    shaft_half = sq * 0.085
    bx, by = tx - ux * head_len, ty - uy * head_len    # where the head begins
    cr.set_source_rgba(rgb[0], rgb[1], rgb[2], alpha)
    cr.move_to(sx + px * shaft_half, sy + py * shaft_half)
    cr.line_to(bx + px * shaft_half, by + py * shaft_half)
    cr.line_to(bx + px * head_half, by + py * head_half)
    cr.line_to(tx, ty)
    cr.line_to(bx - px * head_half, by - py * head_half)
    cr.line_to(bx - px * shaft_half, by - py * shaft_half)
    cr.line_to(sx - px * shaft_half, sy - py * shaft_half)
    cr.close_path()
    cr.fill()


def draw_circle(cr, sq, name, flipped, rgb, alpha=0.8):
    cx, cy = _centre(name, flipped, sq)
    cr.set_source_rgba(rgb[0], rgb[1], rgb[2], alpha)
    cr.set_line_width(sq * 0.06)
    cr.arc(cx, cy, sq * 0.45, 0, 6.283185307)
    cr.stroke()


def draw_board(cr, size, grid, flipped, selected_sq, targets, last_move, notes, best_move):
    sq = size / 8.0
    cr.select_font_face("Sans", cairo.FONT_SLANT_NORMAL, cairo.FONT_WEIGHT_BOLD)

    for r in range(8):
        for c in range(8):
            name = screen_to_sq(r, c, flipped)
            br, bc = (7 - r, 7 - c) if flipped else (r, c)  # index into the FEN grid
            light = (r + c) % 2 == 0
            if name == selected_sq:
                cr.set_source_rgb(0.95, 0.85, 0.30)
            elif last_move and name in (last_move[:2], last_move[2:4]):
                cr.set_source_rgb(0.78, 0.86, 0.45) if light else cr.set_source_rgb(0.65, 0.75, 0.32)
            else:
                cr.set_source_rgb(0.93, 0.85, 0.71) if light else cr.set_source_rgb(0.71, 0.53, 0.39)

            cr.rectangle(c * sq, r * sq, sq, sq)
            cr.fill()

            # Legal move target dot
            if name in targets:
                cr.set_source_rgba(0.15, 0.65, 0.25, 0.75)
                cr.arc((c + 0.5) * sq, (r + 0.5) * sq, sq * 0.18, 0, 6.283)
                cr.fill()

            # Coordinate labels (follow the board orientation)
            if c == 0:
                cr.set_source_rgb(0.25, 0.25, 0.25)
                cr.set_font_size(sq * 0.16)
                cr.move_to(c * sq + 3, r * sq + sq * 0.20)
                cr.show_text(name[1])
            if r == 7:
                cr.set_source_rgb(0.25, 0.25, 0.25)
                cr.set_font_size(sq * 0.16)
                cr.move_to((c + 1) * sq - sq * 0.20, (r + 1) * sq - 4)
                cr.show_text(name[0])

            # Piece token
            piece = grid[br][bc]
            if piece:
                is_white = piece.isupper()
                cx, cy = (c + 0.5) * sq, (r + 0.5) * sq

                if is_white:
                    cr.set_source_rgb(0.98, 0.98, 0.96)
                else:
                    cr.set_source_rgb(0.16, 0.16, 0.18)
                cr.arc(cx, cy, sq * 0.39, 0, 6.283)
                cr.fill_preserve()

                cr.set_line_width(2.2)
                if is_white:
                    cr.set_source_rgb(0.20, 0.20, 0.20)
                else:
                    cr.set_source_rgb(0.85, 0.85, 0.85)
                cr.stroke()

                sym, pname = display_piece(piece)

                # Big piece symbol
                cr.set_font_size(sq * 0.38)
                ext = cr.text_extents(sym)
                if is_white:
                    cr.set_source_rgb(0.10, 0.10, 0.10)
                else:
                    cr.set_source_rgb(0.96, 0.96, 0.96)
                cr.move_to(cx - ext.width / 2 - ext.x_bearing, cy - ext.height / 2 - ext.y_bearing - sq * 0.06)
                cr.show_text(sym)

                # Name underneath, shrunk if needed so it stays inside the disc
                font = sq * 0.13
                cr.set_font_size(font)
                sext = cr.text_extents(pname)
                max_w = sq * 0.60
                if sext.width > max_w:
                    font *= max_w / sext.width
                    cr.set_font_size(font)
                    sext = cr.text_extents(pname)
                cr.move_to(cx - sext.width / 2 - sext.x_bearing, cy + sq * 0.23)
                cr.show_text(pname)

    # Overlays: circles, user arrows, engine best move, live preview while dragging
    for name, brush in notes.circles:
        draw_circle(cr, sq, name, flipped, BRUSHES[brush])
    for frm, to, brush in notes.arrows:
        draw_arrow(cr, sq, frm, to, flipped, BRUSHES[brush])
    if best_move and len(best_move) >= 4:
        draw_arrow(cr, sq, best_move[:2], best_move[2:4], flipped, BEST_COLOR, 0.85)
    if notes.drag_from is not None and notes.drag_to is not None:
        rgb = BRUSHES[notes.drag_brush]
        if notes.drag_to == notes.drag_from:
            draw_circle(cr, sq, notes.drag_from, flipped, rgb, 0.5)
        else:
            draw_arrow(cr, sq, notes.drag_from, notes.drag_to, flipped, rgb, 0.55)


# ---------------------------------------------------------------------------
# Engine
# ---------------------------------------------------------------------------
class UCIEngine:
    def __init__(self, exe_path):
        self.proc = subprocess.Popen(
            [exe_path],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            universal_newlines=True,
            bufsize=1,
        )
        self.lock = threading.Lock()        # one conversation with the engine at a time
        self._wlock = threading.Lock()      # keeps single commands from interleaving
        self._stop_lock = threading.Lock()  # guards _active_cancel
        self._active_cancel = None          # cancel token of the search that is running now
        self.send("uci")
        self.wait_for("uciok")
        self.send("setoption name UCI_Variant value dragonanga")
        self.wait_ready()

    def send(self, cmd):
        with self._wlock:
            self.proc.stdin.write(cmd + "\n")
            self.proc.stdin.flush()

    def close(self):
        try:
            self.send("quit")
        except Exception:
            pass
        try:
            self.proc.terminate()
        except Exception:
            pass

    def wait_for(self, token):
        lines = []
        while True:
            line = self.proc.stdout.readline()
            if not line:
                break
            line = line.strip()
            lines.append(line)
            if line.startswith(token):
                break
        return lines

    def wait_ready(self):
        self.send("isready")
        return self.wait_for("readyok")

    def new_game(self):
        with self.lock:
            self.send("ucinewgame")
            self.wait_ready()

    def get_state(self, moves):
        """Ask Fairy-Stockfish for the current FEN and exact legal moves."""
        with self.lock:
            pos_cmd = "position startpos"
            if moves:
                pos_cmd += " moves " + " ".join(moves)
            self.send(pos_cmd)
            self.send("d")
            d_lines = self.wait_ready()

            fen = ""
            checkers = ""
            for line in d_lines:
                if line.startswith("Fen:"):
                    fen = line.split("Fen:", 1)[1].strip()
                elif line.startswith("Checkers:"):
                    checkers = line.split("Checkers:", 1)[1].strip()

            self.send("go perft 1")
            # Wait for the background worker thread to finish printing all moves
            perft_lines = self.wait_for("Nodes searched:")
            self.wait_ready()

            legal_moves = []
            for line in perft_lines:
                m = re.match(r"^([a-h][1-8][a-h][1-8][a-zA-Z]?)\s*:", line)
                if m:
                    legal_moves.append(m.group(1))

            print(f"[ENGINE STATE] FEN: {fen} | Legal Moves: {len(legal_moves)} | Checkers: '{checkers}'")
            return fen, legal_moves, bool(checkers)

    def search(self, moves, movetime_ms, info_callback, cancel=None):
        """Run an engine search and return bestmove.

        movetime_ms=None means 'go infinite' (background analysis); it only ends
        when request_stop(cancel) is called.  If `cancel` is already set by the
        time this search gets its turn, nothing is run.
        """
        with self.lock:
            if cancel is not None and cancel.is_set():
                return None
            pos_cmd = "position startpos"
            if moves:
                pos_cmd += " moves " + " ".join(moves)
            self.send(pos_cmd)
            self.send("go infinite" if movetime_ms is None else f"go movetime {movetime_ms}")
            with self._stop_lock:
                self._active_cancel = cancel
                if cancel is not None and cancel.is_set():
                    self.send("stop")  # stop was requested while we were starting up

            bestmove = None
            while True:
                line = self.proc.stdout.readline()
                if not line:
                    break
                line = line.strip()
                if line.startswith("info ") and "score " in line:
                    info_callback(line)
                elif line.startswith("bestmove"):
                    parts = line.split()
                    bestmove = parts[1] if len(parts) > 1 else None
                    break
            with self._stop_lock:
                self._active_cancel = None
            return bestmove

    def request_stop(self, cancel):
        """Ask the search that owns `cancel` to finish (safe from any thread)."""
        cancel.set()
        with self._stop_lock:
            if self._active_cancel is cancel:
                self.send("stop")


# ---------------------------------------------------------------------------
# Window
# ---------------------------------------------------------------------------
class DragonangaWindow(Gtk.Window):
    def __init__(self, engine_path):
        super().__init__(title="Dragonanga Engine Tester (Fairy-Stockfish)")
        self.set_default_size(680, 800)
        self.connect("destroy", self.on_destroy)

        self.engine = UCIEngine(engine_path)
        self.moves = []
        self.fen = ""
        self.legal_moves = []
        self.in_check = False
        self.selected_sq = None
        self.human_color = "w"
        self.thinking = False
        self.last_move = None
        self.flipped = False
        self.notes = Annotations()
        self.best_move = None
        self.analysis_cancel = None
        self.analysis_gen = 0

        vbox = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        vbox.set_margin_top(8)
        vbox.set_margin_bottom(8)
        vbox.set_margin_start(8)
        vbox.set_margin_end(8)
        self.add(vbox)

        # Top controls
        ctrl_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        vbox.pack_start(ctrl_box, False, False, 0)

        btn_white = Gtk.Button(label="New Game (Play White)")
        btn_white.connect("clicked", lambda _: self.start_new_game("w"))
        ctrl_box.pack_start(btn_white, False, False, 0)

        btn_black = Gtk.Button(label="New Game (Play Black)")
        btn_black.connect("clicked", lambda _: self.start_new_game("b"))
        ctrl_box.pack_start(btn_black, False, False, 0)

        btn_undo = Gtk.Button(label="Undo Turn")
        btn_undo.connect("clicked", self.on_undo)
        ctrl_box.pack_start(btn_undo, False, False, 0)

        ctrl_box.pack_start(Gtk.Label(label="Think Time (sec):"), False, False, 4)
        self.time_spin = Gtk.SpinButton.new_with_range(0.5, 30.0, 0.5)
        self.time_spin.set_value(2.0)
        ctrl_box.pack_start(self.time_spin, False, False, 0)

        # Second row: view options
        view_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        vbox.pack_start(view_box, False, False, 0)

        btn_flip = Gtk.Button(label="Flip Board")
        btn_flip.connect("clicked", self.on_flip)
        view_box.pack_start(btn_flip, False, False, 0)

        self.best_chk = Gtk.CheckButton(label="Show best move")
        self.best_chk.connect("toggled", self.on_best_toggled)
        view_box.pack_start(self.best_chk, False, False, 0)

        hint = Gtk.Label(label="Right-click drag = arrow (Shift red, Ctrl orange, Alt purple) | left click clears")
        hint.set_xalign(0)
        view_box.pack_start(hint, False, False, 8)

        # Status & Eval labels
        self.status_label = Gtk.Label(label="Ready")
        self.status_label.set_xalign(0)
        vbox.pack_start(self.status_label, False, False, 2)

        self.eval_label = Gtk.Label(label="Eval (White's view): -- | Depth: -- | Line: --")
        self.eval_label.set_xalign(0)
        vbox.pack_start(self.eval_label, False, False, 2)

        # Board drawing area
        self.area = Gtk.DrawingArea()
        self.area.set_size_request(640, 640)
        self.area.add_events(
            Gdk.EventMask.BUTTON_PRESS_MASK
            | Gdk.EventMask.BUTTON_RELEASE_MASK
            | Gdk.EventMask.POINTER_MOTION_MASK
        )
        self.area.connect("draw", self.on_draw)
        self.area.connect("button-press-event", self.on_press)
        self.area.connect("button-release-event", self.on_release)
        self.area.connect("motion-notify-event", self.on_motion)
        vbox.pack_start(self.area, True, True, 0)

        self.start_new_game("w")

    def on_destroy(self, *_):
        try:
            self.cancel_analysis()
            self.engine.close()
        finally:
            Gtk.main_quit()

    # ----- game flow -------------------------------------------------------
    def start_new_game(self, human_color):
        if self.thinking:
            return
        self.human_color = human_color
        self.flipped = human_color == "b"  # your side at the bottom
        self.moves = []
        self.selected_sq = None
        self.last_move = None
        self.notes.clear()
        self.cancel_analysis()
        self.engine.new_game()
        self.eval_label.set_text("Eval (White's view): +0.00 | Starting position")
        self.sync_board()
        if self.turn_color() != self.human_color:
            self.trigger_engine_move()

    def on_undo(self, _):
        if self.thinking or len(self.moves) < 2:
            return
        self.moves = self.moves[:-2]
        self.selected_sq = None
        self.last_move = self.moves[-1] if self.moves else None
        self.notes.clear()
        self.sync_board()

    def on_flip(self, _):
        self.flipped = not self.flipped
        self.area.queue_draw()

    def turn_color(self):
        parts = self.fen.split()
        return parts[1] if len(parts) > 1 else "w"

    def parse_fen_grid(self):
        grid = [[None for _ in range(8)] for _ in range(8)]
        if not self.fen:
            return grid
        rows = self.fen.split()[0].split("/")
        for r, row_str in enumerate(rows[:8]):
            c = 0
            for ch in row_str:
                if ch.isdigit():
                    c += int(ch)
                else:
                    if c < 8:
                        grid[r][c] = ch
                    c += 1
        return grid

    def sync_board(self):
        self.cancel_analysis()  # the engine must be idle before we query it
        self.fen, self.legal_moves, self.in_check = self.engine.get_state(self.moves)
        turn = "White" if self.turn_color() == "w" else "Black"
        if not self.legal_moves:
            if self.in_check:
                self.status_label.set_text(f"Game Over — Checkmate! ({turn} has no moves)")
            else:
                self.status_label.set_text(f"Game Over — Baremate / Stalemate! ({turn} has no moves)")
        else:
            chk = " (IN CHECK!)" if self.in_check else ""
            self.status_label.set_text(f"Turn: {turn}{chk} | Legal moves: {len(self.legal_moves)} | FEN: {self.fen}")
        self.area.queue_draw()
        self.maybe_start_analysis()

    # ----- background analysis (best-move arrow) -----------------------------
    def cancel_analysis(self):
        self.analysis_gen += 1  # late results from the old search are ignored
        if self.analysis_cancel is not None:
            self.engine.request_stop(self.analysis_cancel)
            self.analysis_cancel = None
        self.best_move = None

    def maybe_start_analysis(self):
        if (
            not self.best_chk.get_active()
            or self.thinking
            or not self.legal_moves
            or self.turn_color() != self.human_color
        ):
            return
        cancel = threading.Event()
        self.analysis_cancel = cancel
        gen = self.analysis_gen
        moves = list(self.moves)
        stm = self.turn_color()

        def on_info(line):
            info = parse_info_line(line, stm)
            if info:
                GLib.idle_add(self.on_analysis_info, gen, info)

        def worker():
            self.engine.search(moves, None, on_info, cancel=cancel)

        threading.Thread(target=worker, daemon=True).start()

    def on_analysis_info(self, gen, info):
        if gen != self.analysis_gen:
            return False
        self.eval_label.set_text(format_eval(info))
        self.best_move = info["pv"][0] if info["pv"] else None
        self.area.queue_draw()
        return False

    def on_best_toggled(self, _):
        self.cancel_analysis()
        self.maybe_start_analysis()
        self.area.queue_draw()

    # ----- mouse -------------------------------------------------------------
    def event_to_sq(self, x, y):
        alloc = self.area.get_allocation()
        return point_to_sq(x, y, min(alloc.width, alloc.height), self.flipped)

    @staticmethod
    def brush_for(state):
        if state & Gdk.ModifierType.SHIFT_MASK:
            return "red"
        if state & Gdk.ModifierType.CONTROL_MASK:
            return "orange"
        if state & Gdk.ModifierType.MOD1_MASK:
            return "purple"
        return "green"

    def on_press(self, widget, event):
        sq = self.event_to_sq(event.x, event.y)
        if event.button == 3:
            if sq:
                self.notes.begin(sq, self.brush_for(event.state))
                self.area.queue_draw()
        elif event.button == 1:
            if self.notes.clear():
                self.area.queue_draw()
            self.handle_left_click(sq)
        return True

    def on_motion(self, widget, event):
        if self.notes.drag_from is not None:
            sq = self.event_to_sq(event.x, event.y)
            if sq != self.notes.drag_to:
                self.notes.update(sq)
                self.area.queue_draw()
        return True

    def on_release(self, widget, event):
        if event.button == 3 and self.notes.drag_from is not None:
            self.notes.finish(self.event_to_sq(event.x, event.y))
            self.area.queue_draw()
        return True

    def handle_left_click(self, clicked):
        if clicked is None or self.thinking or self.turn_color() != self.human_color or not self.legal_moves:
            return

        if self.selected_sq:
            matching = [m for m in self.legal_moves if m.startswith(self.selected_sq + clicked)]
            if matching:
                chosen_move = matching[0]
                if len(matching) > 1:
                    chosen_move = self.ask_promotion(matching)
                self.selected_sq = None
                self.make_move(chosen_move)
                return

        # Select piece if it has legal moves starting from this square
        if any(m.startswith(clicked) for m in self.legal_moves):
            self.selected_sq = clicked
        else:
            self.selected_sq = None
        self.area.queue_draw()

    def ask_promotion(self, matching_moves):
        dialog = Gtk.Dialog(title="Promote Piece", transient_for=self, flags=0)
        box = dialog.get_content_area()
        box.set_spacing(6)
        box.pack_start(Gtk.Label(label="Choose promotion piece:"), False, False, 4)
        for idx, m in enumerate(matching_moves):
            sym, pname = display_piece(m[4:])
            dialog.add_button(f"{sym} ({pname})", idx)
        dialog.show_all()
        resp = dialog.run()
        dialog.destroy()
        if 0 <= resp < len(matching_moves):
            return matching_moves[resp]
        return matching_moves[0]

    def make_move(self, uci_move):
        self.moves.append(uci_move)
        self.last_move = uci_move
        self.notes.clear()
        self.sync_board()
        if self.legal_moves and self.turn_color() != self.human_color:
            self.trigger_engine_move()

    def trigger_engine_move(self):
        self.thinking = True
        self.status_label.set_text("Fairy-Stockfish is thinking...")
        movetime_ms = int(self.time_spin.get_value() * 1000)
        stm = self.turn_color()
        moves = list(self.moves)

        def parse_info(line):
            info = parse_info_line(line, stm)
            if info:
                GLib.idle_add(self.eval_label.set_text, format_eval(info))

        def worker():
            best = self.engine.search(moves, movetime_ms, parse_info)
            GLib.idle_add(self.finish_engine_move, best)

        threading.Thread(target=worker, daemon=True).start()

    def finish_engine_move(self, bestmove):
        self.thinking = False
        if bestmove and bestmove != "(none)":
            self.moves.append(bestmove)
            self.last_move = bestmove
        self.sync_board()

    # ----- drawing -----------------------------------------------------------
    def on_draw(self, widget, cr):
        alloc = self.area.get_allocation()
        size = min(alloc.width, alloc.height)

        targets = set()
        if self.selected_sq:
            for m in self.legal_moves:
                if m.startswith(self.selected_sq):
                    targets.add(m[2:4])

        draw_board(
            cr, size, self.parse_fen_grid(), self.flipped, self.selected_sq, targets,
            self.last_move, self.notes, self.best_move if self.best_chk.get_active() else None,
        )


def pick_engine_executable():
    dialog = Gtk.FileChooserDialog(
        title="Select your compiled Fairy-Stockfish .exe",
        action=Gtk.FileChooserAction.OPEN,
    )
    dialog.add_buttons(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK)
    resp = dialog.run()
    path = dialog.get_filename() if resp == Gtk.ResponseType.OK else None
    dialog.destroy()
    return path


if __name__ == "__main__":
    exe = pick_engine_executable()
    if exe and os.path.isfile(exe):
        win = DragonangaWindow(exe)
        win.show_all()
        Gtk.main()