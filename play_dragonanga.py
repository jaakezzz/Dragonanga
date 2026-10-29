"""Dragonanga engine tester (Fairy-Stockfish).

Modes (the three buttons never reset the game, so you can swap sides mid-game)
  * Play as White / Play as Black   the engine plays the other side (board turns to match)
  * Analysis Mode                   you move both sides, the engine never plays by itself
  * New Game                        back to the starting position, keeps the current mode

Position
  * Import Position   paste a FEN written with the designer letters
                      (S Soldier, G Guard, E Elephant, H Horse, D Dragon,
                       Q Queen Fairy, K King, F Fairy, M Minister)
                      or raw engine letters; the app converts it for the engine.
  * The FEN in the status line is shown in designer letters too.

Analysis
  * Show best move   blue arrow for the engine's best move on your turn
  * Show lines       the engine's 3 best continuations, written in designer notation
                     (piece letter + square, x = capture, =F promotion, + check, # mate)
  * Eval is always from White's point of view: + = White ahead, - = Black ahead

Drawing
  * Right click + drag   arrow (Shift red, Ctrl orange, Alt purple); right click a square = circle
  * Left click           select / move, and clears the drawings
"""
import html
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
# Piece display and notation.  The ENGINE letters are the ones in variant.cpp,
# the FEN and the UCI promotion suffixes.  The DESIGNER letters are what you
# see on screen, in the FEN box and in the move lists.
#   engine letter -> (designer letter, name)
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
ENGINE_TO_DESIGNER = {e: d for e, (d, _) in PIECE_DISPLAY.items()}
DESIGNER_TO_ENGINE = {d: e for e, d in ENGINE_TO_DESIGNER.items()}
DESIGNER_ONLY = set(DESIGNER_TO_ENGINE) - set(ENGINE_TO_DESIGNER)  # S G Q
ENGINE_ONLY = set(ENGINE_TO_DESIGNER) - set(DESIGNER_TO_ENGINE)    # P I C

AUTO, DESIGNER, ENGINE = "auto", "designer", "engine"
NOTATION_CHOICES = (
    ("Auto-detect", AUTO),
    ("Designer letters (S G E H D Q K F M)", DESIGNER),
    ("Engine letters (P I E H D K C F M)", ENGINE),
)

MODES = {
    "white": ({"w"}, "Playing White"),
    "black": ({"b"}, "Playing Black"),
    "analysis": ({"w", "b"}, "Analysis (you move both sides)"),
}

NUM_LINES = 3      # "Show lines" shows this many continuations
MAX_PLIES = 10     # plies shown per line


def display_piece(letter):
    """Engine letter (any case) -> (designer letter, name) for drawing."""
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


def other_side(side):
    return "b" if side == "w" else "w"


def position_cmd(start_fen, moves):
    """UCI 'position' command for the start position (or an imported FEN) plus moves."""
    base = f"position fen {start_fen}" if start_fen else "position startpos"
    return base + (" moves " + " ".join(moves) if moves else "")


def undo_length(start_stm, n_moves, human_sides):
    """How many plies to keep after 'Undo Turn', or None if there is nothing to undo.

    Takes back plies until it is a human side's turn again (so against the engine
    that is your move and its reply; in Analysis Mode it is a single ply)."""
    def stm_after(k):
        return start_stm if k % 2 == 0 else other_side(start_stm)
    if n_moves == 0:
        return None
    k = n_moves - 1
    while k > 0 and stm_after(k) not in human_sides:
        k -= 1
    return k if stm_after(k) in human_sides else None


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
    mpv_m = re.search(r"\bmultipv\s+(\d+)", line)
    pv_m = re.search(r"\bpv\s+(.+)$", line)
    return {
        "depth": int(depth_m.group(1)) if depth_m else None,
        "multipv": int(mpv_m.group(1)) if mpv_m else 1,
        "score": score,
        "pv": pv_m.group(1).split() if pv_m else [],
    }


def format_eval(info, show_line=True):
    depth = info["depth"] if info["depth"] is not None else "?"
    text = f"Eval (White's view): {info['score']} | Depth: {depth}"
    if show_line and info.get("text"):
        text += f" | Line: {info['text']}"
    return text


def format_line_row(info):
    depth = info["depth"] if info["depth"] is not None else "?"
    return f"{info['score']:>7}  d{depth:<3} {info.get('text', '')}"


# ----- FEN / letter conversion ---------------------------------------------
def convert_letters(placement, table):
    """Translate the piece letters of a FEN piece-placement field, keeping case."""
    out = []
    for ch in placement:
        if ch.isalpha() and ch.upper() in table:
            t = table[ch.upper()]
            out.append(t if ch.isupper() else t.lower())
        else:
            out.append(ch)
    return "".join(out)


def engine_fen_to_designer(fen):
    """Engine FEN -> same FEN written with designer letters (only the placement changes)."""
    parts = fen.split()
    if parts:
        parts[0] = convert_letters(parts[0], ENGINE_TO_DESIGNER)
    return " ".join(parts)


def _compress_rank(squares):
    out, empty = [], 0
    for sq in squares:
        if sq is None:
            empty += 1
        else:
            if empty:
                out.append(str(empty))
                empty = 0
            out.append(sq)
    if empty:
        out.append(str(empty))
    return "".join(out)


def parse_import_fen(text, notation=AUTO):
    """Turn a pasted FEN into an engine FEN.  Returns (engine_fen, notation_used).

    Raises ValueError with a readable message if the text is not a usable position.
    The engine itself accepts nonsense silently (missing royals, short ranks...), so
    everything is checked here first."""
    fields = text.split()
    if not fields:
        raise ValueError("Paste a FEN first.")
    placement = fields[0]
    letters = {ch.upper() for ch in placement if ch.isalpha()}

    if notation == AUTO:
        has_designer, has_engine = bool(letters & DESIGNER_ONLY), bool(letters & ENGINE_ONLY)
        if has_designer and has_engine:
            raise ValueError(
                "This FEN mixes designer letters (S, G, Q) with engine letters (P, I, C). "
                "Use one notation only."
            )
        notation = DESIGNER if has_designer else ENGINE
    # letter -> engine letter; engine notation is already what the engine wants
    table = DESIGNER_TO_ENGINE if notation == DESIGNER else {e: e for e in ENGINE_TO_DESIGNER}
    for ch in sorted(letters):
        if ch in table:
            continue
        if notation == DESIGNER and ch in ENGINE_ONLY:
            raise ValueError(
                f"'{ch}' is an engine letter (in designer notation it is {ENGINE_TO_DESIGNER[ch]}). "
                "Pick 'Engine letters' if this FEN came from the engine."
            )
        if notation == ENGINE and ch in DESIGNER_ONLY:
            raise ValueError(
                f"'{ch}' is a designer letter (the engine writes it {DESIGNER_TO_ENGINE[ch]}). "
                "Pick 'Designer letters' if this FEN uses designer notation."
            )
        raise ValueError(f"Unknown piece letter '{ch}'.")

    ranks = placement.split("/")
    if len(ranks) != 8:
        raise ValueError(f"A FEN needs 8 ranks separated by '/', this has {len(ranks)}.")
    rows = []
    for i, rank in enumerate(ranks):
        number = 8 - i
        squares = []
        for ch in rank:
            if ch in "12345678":
                squares.extend([None] * int(ch))
            elif ch.isalpha():
                t = table[ch.upper()]
                squares.append(t if ch.isupper() else t.lower())
            else:
                raise ValueError(f"Rank {number}: unexpected character '{ch}'.")
        if len(squares) != 8:
            raise ValueError(f"Rank {number} covers {len(squares)} squares instead of 8.")
        rows.append(squares)
    engine_placement = "/".join(_compress_rank(r) for r in rows)

    white_royals, black_royals = engine_placement.count("K"), engine_placement.count("k")
    if white_royals != 1 or black_royals != 1:
        raise ValueError(
            "Each side needs exactly one Queen Fairy (Q in designer letters, K in engine letters); "
            f"found {white_royals} for White and {black_royals} for Black."
        )

    stm = fields[1].lower() if len(fields) > 1 else "w"
    if stm not in ("w", "b"):
        raise ValueError(f"Side to move must be 'w' or 'b', not '{fields[1]}'.")
    half = fields[4] if len(fields) > 4 and fields[4].isdigit() else "0"
    full = fields[5] if len(fields) > 5 and fields[5].isdigit() and int(fields[5]) > 0 else "1"
    return f"{engine_placement} {stm} - - {half} {full}", notation


def fen_to_board(fen):
    """FEN -> {square: engine letter}."""
    board = {}
    for r, row in enumerate(fen.split()[0].split("/")[:8]):
        c = 0
        for ch in row:
            if ch.isdigit():
                c += int(ch)
            else:
                if c < 8:
                    board[f"{chr(97 + c)}{8 - r}"] = ch
                c += 1
    return board


# ----- designer move notation ----------------------------------------------
def designer_move(board, legal_before, move, check=False, mate=False):
    """One UCI move -> designer notation, e.g. 'Gc3', 'Ebxd4', 'Sc5=F', 'Ka7#'.

    board         {square: engine letter} before the move
    legal_before  every legal UCI move in that position (needed to disambiguate)
    The piece letter is always written (the Soldier is S); a file, rank or full square
    is added only when another identical piece could also reach the square."""
    frm, to, promo = move[:2], move[2:4], move[4:]
    piece = board.get(frm)
    if piece is None:
        raise ValueError(f"no piece on {frm}")
    sym = display_piece(piece)[0]
    rivals = {m[:2] for m in legal_before if m[2:4] == to and m[:2] != frm and board.get(m[:2]) == piece}
    dis = ""
    if rivals:
        if not any(r[0] == frm[0] for r in rivals):
            dis = frm[0]
        elif not any(r[1] == frm[1] for r in rivals):
            dis = frm[1]
        else:
            dis = frm
    text = sym + dis + ("x" if to in board else "") + to
    if promo:
        text += "=" + display_piece(promo)[0]
    if mate:
        text += "#"
    elif check:
        text += "+"
    return text


def number_line(sans, stm, fullmove):
    """['Gc3','Sc6','Gb4'] -> '1.Gc3 Sc6 2.Gb4' (a Black-first line starts '1...Sc6')."""
    parts = []
    side, num = stm, fullmove
    for i, mv in enumerate(sans):
        if side == "w":
            parts.append(f"{num}.{mv}")
        elif i == 0:
            parts.append(f"{num}...{mv}")
        else:
            parts.append(mv)
        if side == "b":
            num += 1
        side = other_side(side)
    return " ".join(parts)


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
    cr.new_sub_path()
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
                cr.new_sub_path()
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

    def get_state(self, moves, start_fen=None, quiet=False):
        """Ask Fairy-Stockfish for the current FEN, exact legal moves and whether the
        side to move is in check.  start_fen=None means the normal start position."""
        with self.lock:
            self.send(position_cmd(start_fen, moves))
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

            if not quiet:
                print(f"[ENGINE STATE] FEN: {fen} | Legal Moves: {len(legal_moves)} | Checkers: '{checkers}'")
            return fen, legal_moves, bool(checkers)

    def search(self, moves, movetime_ms, info_callback, cancel=None, multipv=1, start_fen=None):
        """Run an engine search and return bestmove.

        movetime_ms=None means 'go infinite' (background analysis); it only ends
        when request_stop(cancel) is called.  If `cancel` is already set by the
        time this search gets its turn, nothing is run.
        """
        with self.lock:
            if cancel is not None and cancel.is_set():
                return None
            self.send(f"setoption name MultiPV value {multipv}")
            self.send(position_cmd(start_fen, moves))
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


class NotationConverter:
    """Writes engine moves in designer notation.

    Disambiguation ('Ebd4' vs 'Efd4') and check/mate marks need the legal moves of
    every position along a line, so a second engine process is used purely as a rules
    oracle (the search engine is busy searching).  Results are cached."""

    CACHE_LIMIT = 4000

    def __init__(self, oracle):
        self.oracle = oracle
        self.cache = {}

    def state(self, start_fen, moves):
        key = (start_fen, tuple(moves))
        hit = self.cache.get(key)
        if hit is None:
            hit = self.oracle.get_state(list(moves), start_fen, quiet=True)
            if not hit[0]:
                raise RuntimeError("the rules engine returned no position")
            if len(self.cache) >= self.CACHE_LIMIT:
                self.cache.clear()
            self.cache[key] = hit
        return hit

    def convert(self, start_fen, base_moves, pv, should_stop=lambda: False):
        """UCI moves `pv`, played from the position after `base_moves`, -> list of designer
        notation strings.  Returns None if should_stop() became true; raises on illegal moves."""
        moves = list(base_moves)
        fen, legal, _ = self.state(start_fen, moves)
        sans = []
        for mv in pv:
            if should_stop():
                return None
            if mv not in legal:
                raise ValueError(f"{mv} is not a legal move in {fen}")
            board = fen_to_board(fen)
            moves.append(mv)
            next_fen, next_legal, next_check = self.state(start_fen, moves)
            sans.append(designer_move(board, legal, mv, check=next_check, mate=next_check and not next_legal))
            fen, legal = next_fen, next_legal
        return sans


class InfoPump:
    """Receives raw engine 'info' lines on the search thread and, on its own thread,
    converts the principal variations to designer notation at most ~8 times a second,
    then hands the finished results to `publish` (a list of dicts sorted by line number)."""

    def __init__(self, converter, start_fen, moves, stm, fullmove, cancel, publish, max_lines, interval=0.12):
        self.converter, self.start_fen, self.moves = converter, start_fen, moves
        self.stm, self.fullmove = stm, fullmove
        self.cancel, self.publish = cancel, publish
        self.max_lines, self.interval = max_lines, interval
        self.latest = {}
        self.lock = threading.Lock()
        self.wake = threading.Event()
        self.done = threading.Event()

    def start(self):
        threading.Thread(target=self._run, daemon=True).start()

    def close(self):
        self.done.set()
        self.wake.set()

    def feed(self, line):
        info = parse_info_line(line, self.stm)
        if info is None or info["multipv"] > self.max_lines:
            return
        with self.lock:
            self.latest[info["multipv"]] = info
        self.wake.set()

    def _stopped(self):
        return self.done.is_set() or self.cancel.is_set()

    def _text(self, info):
        pv = info["pv"][:MAX_PLIES]
        more = "…" if len(info["pv"]) > MAX_PLIES else ""
        try:
            sans = self.converter.convert(self.start_fen, self.moves, pv, self._stopped)
        except Exception:
            sans = None
        if sans is None:
            return None if self._stopped() else " ".join(pv) + more  # fall back to engine notation
        return number_line(sans, self.stm, self.fullmove) + more

    def _run(self):
        while not self._stopped():
            if not self.wake.wait(0.25):
                continue
            self.wake.clear()
            if self._stopped():
                return
            with self.lock:
                snapshot = [self.latest[k] for k in sorted(self.latest)]
            results = []
            for info in snapshot:
                text = self._text(info)
                if text is None:
                    return
                results.append(dict(info, text=text))
            if results:
                self.publish(results)
            self.done.wait(self.interval)


# ---------------------------------------------------------------------------
# Window
# ---------------------------------------------------------------------------
class DragonangaWindow(Gtk.Window):
    def __init__(self, engine_path):
        super().__init__(title="Dragonanga Engine Tester (Fairy-Stockfish)")
        self.set_default_size(660, 720)
        self.connect("destroy", self.on_destroy)

        self.engine = UCIEngine(engine_path)   # searches
        self.oracle = UCIEngine(engine_path)   # rules questions for the notation converter
        self.converter = NotationConverter(self.oracle)

        self.start_fen = None                  # None = normal start position, else an imported engine FEN
        self.start_stm = "w"
        self.moves = []
        self.fen = ""
        self.legal_moves = []
        self.in_check = False
        self.selected_sq = None
        self.mode = None
        self.human_sides = {"w"}
        self.thinking = False
        self.engine_gen = 0
        self.engine_cancel = None
        self.last_move = None
        self.flipped = False
        self.notes = Annotations()
        self.best_move = None
        self.analysis_lines = []
        self.analysis_cancel = None
        self.analysis_gen = 0

        vbox = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        vbox.set_margin_top(8)
        vbox.set_margin_bottom(8)
        vbox.set_margin_start(8)
        vbox.set_margin_end(8)
        self.add(vbox)

        # Row 1: game and mode
        row1 = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        vbox.pack_start(row1, False, False, 0)
        for label, handler in (
            ("New Game", lambda _: self.new_game()),
            ("Play as White", lambda _: self.set_mode("white")),
            ("Play as Black", lambda _: self.set_mode("black")),
            ("Analysis Mode", lambda _: self.set_mode("analysis")),
            ("Undo Turn", self.on_undo),
        ):
            btn = Gtk.Button(label=label)
            btn.connect("clicked", handler)
            row1.pack_start(btn, False, False, 0)

        # Row 2: position and view
        row2 = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        vbox.pack_start(row2, False, False, 0)

        btn_import = Gtk.Button(label="Import Position")
        btn_import.connect("clicked", self.on_import)
        row2.pack_start(btn_import, False, False, 0)

        btn_flip = Gtk.Button(label="Flip Board")
        btn_flip.connect("clicked", self.on_flip)
        row2.pack_start(btn_flip, False, False, 0)

        self.best_chk = Gtk.CheckButton(label="Show best move")
        self.best_chk.connect("toggled", self.on_analysis_option_toggled)
        row2.pack_start(self.best_chk, False, False, 0)

        self.lines_chk = Gtk.CheckButton(label="Show lines")
        self.lines_chk.connect("toggled", self.on_analysis_option_toggled)
        row2.pack_start(self.lines_chk, False, False, 0)

        row2.pack_start(Gtk.Label(label="Think Time (sec):"), False, False, 4)
        self.time_spin = Gtk.SpinButton.new_with_range(0.5, 30.0, 0.5)
        self.time_spin.set_value(2.0)
        row2.pack_start(self.time_spin, False, False, 0)

        hint = Gtk.Label(label="Right-click drag = arrow (Shift red, Ctrl orange, Alt purple) | left click clears")
        hint.set_xalign(0)
        vbox.pack_start(hint, False, False, 0)

        # Status & Eval labels
        self.status_label = Gtk.Label(label="Ready")
        self.status_label.set_xalign(0)
        vbox.pack_start(self.status_label, False, False, 2)

        self.eval_label = Gtk.Label(label="Eval (White's view): -- | Depth: -- | Line: --")
        self.eval_label.set_xalign(0)
        vbox.pack_start(self.eval_label, False, False, 2)

        # Engine lines panel (only visible while "Show lines" is ticked)
        self.lines_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
        self.line_labels = []
        for _ in range(NUM_LINES):
            lbl = Gtk.Label(label="")
            lbl.set_xalign(0)
            lbl.show()  # shown individually: show_all() skips the hidden panel below
            self.lines_box.pack_start(lbl, False, False, 0)
            self.line_labels.append(lbl)
        self.lines_box.set_no_show_all(True)
        vbox.pack_start(self.lines_box, False, False, 2)

        # Board drawing area
        self.area = Gtk.DrawingArea()
        self.area.set_size_request(240, 240)
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

        self.set_mode("white")
        self.new_game()

    def on_destroy(self, *_):
        try:
            self.cancel_engine_move()
            self.cancel_analysis()
            self.engine.close()
            self.oracle.close()
        finally:
            Gtk.main_quit()

    # ----- modes and game flow ---------------------------------------------
    def is_human_turn(self):
        return self.turn_color() in self.human_sides

    def set_mode(self, mode):
        """Play as White / Play as Black / Analysis.  Never touches the moves played."""
        if mode == self.mode:
            # Same mode again: just put the board the right way round.
            if mode in ("white", "black"):
                self.flipped = mode == "black"
                self.area.queue_draw()
            return
        self.cancel_engine_move()
        self.mode = mode
        self.human_sides = set(MODES[mode][0])
        if mode == "white":
            self.flipped = False
        elif mode == "black":
            self.flipped = True
        self.selected_sq = None
        self.sync_board()
        self.maybe_engine_move()

    def new_game(self):
        """Back to the starting position; the mode and board orientation stay as they are."""
        self.cancel_engine_move()
        self.cancel_analysis()
        self.start_fen, self.start_stm = None, "w"
        self.moves = []
        self.selected_sq = None
        self.last_move = None
        self.notes.clear()
        self.engine.new_game()
        self.eval_label.set_text("Eval (White's view): +0.00 | Starting position")
        self.sync_board()
        self.maybe_engine_move()

    def on_undo(self, _):
        was_thinking = self.thinking
        self.cancel_engine_move()
        keep = undo_length(self.start_stm, len(self.moves), self.human_sides)
        if keep is None and not was_thinking:
            return
        if keep is not None:
            self.moves = self.moves[:keep]
            self.selected_sq = None
            self.last_move = self.moves[-1] if self.moves else None
            self.notes.clear()
        self.sync_board()
        self.maybe_engine_move()

    def on_flip(self, _):
        self.flipped = not self.flipped
        self.area.queue_draw()

    def turn_color(self):
        parts = self.fen.split()
        return parts[1] if len(parts) > 1 else "w"

    def fullmove_number(self):
        parts = self.fen.split()
        try:
            return max(1, int(parts[5]))
        except (IndexError, ValueError):
            return 1

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
        self.fen, self.legal_moves, self.in_check = self.engine.get_state(self.moves, self.start_fen)
        turn = "White" if self.turn_color() == "w" else "Black"
        mode = MODES[self.mode][1]
        if not self.legal_moves:
            if self.in_check:
                self.status_label.set_text(f"Game Over — Checkmate! ({turn} has no moves)")
            else:
                self.status_label.set_text(f"Game Over — Baremate / Stalemate! ({turn} has no moves)")
        else:
            chk = " (IN CHECK!)" if self.in_check else ""
            self.status_label.set_text(
                f"Mode: {mode} | Turn: {turn}{chk} | Legal moves: {len(self.legal_moves)} | "
                f"FEN: {engine_fen_to_designer(self.fen)}"
            )
        self.area.queue_draw()
        self.maybe_start_analysis()

    # ----- importing a position ------------------------------------------------
    def load_position(self, text, notation=AUTO):
        """Set the board from pasted FEN text.  Returns the notation that was detected.
        Raises ValueError (with a readable message) and changes nothing if it is not usable."""
        engine_fen, used = parse_import_fen(text, notation)
        # The engine happily loads illegal positions, so check the one thing it cannot be
        # trusted with: the side NOT to move must not already be in check.
        fen, _, _ = self.oracle.get_state([], engine_fen, quiet=True)
        if not fen:
            raise ValueError("The engine could not load that position.")
        parts = engine_fen.split()
        parts[1] = other_side(parts[1])
        _, _, opponent_in_check = self.oracle.get_state([], " ".join(parts), quiet=True)
        if opponent_in_check:
            mover = "White" if engine_fen.split()[1] == "w" else "Black"
            raise ValueError(
                f"Illegal position: the side that is not to move is in check ({mover} could capture its "
                "Queen Fairy). Fix the board or the side to move."
            )

        self.cancel_engine_move()
        self.cancel_analysis()
        self.start_fen, self.start_stm = engine_fen, engine_fen.split()[1]
        self.moves = []
        self.selected_sq = None
        self.last_move = None
        self.notes.clear()
        self.engine.new_game()
        self.eval_label.set_text(f"Eval (White's view): -- | Position imported ({used} letters)")
        self.sync_board()
        self.maybe_engine_move()
        return used

    def on_import(self, _):
        dialog = Gtk.Dialog(title="Import Position", transient_for=self, flags=0)
        dialog.add_button("Cancel", Gtk.ResponseType.CANCEL)
        dialog.add_button("Import", Gtk.ResponseType.OK)
        dialog.set_default_response(Gtk.ResponseType.OK)
        box = dialog.get_content_area()
        box.set_spacing(6)

        intro = Gtk.Label(label="Paste a FEN. Designer letters (S G E H D Q K F M) are converted for the engine.")
        intro.set_xalign(0)
        box.pack_start(intro, False, False, 0)

        entry = Gtk.Entry()
        entry.set_width_chars(78)
        entry.set_text(engine_fen_to_designer(self.fen))  # current position, ready to edit
        entry.set_activates_default(True)
        box.pack_start(entry, False, False, 0)

        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        row.pack_start(Gtk.Label(label="Letters used:"), False, False, 0)
        combo = Gtk.ComboBoxText()
        for name, _value in NOTATION_CHOICES:
            combo.append_text(name)
        combo.set_active(0)
        row.pack_start(combo, False, False, 0)
        box.pack_start(row, False, False, 0)

        err = Gtk.Label(label="")
        err.set_xalign(0)
        err.set_line_wrap(True)
        err.set_max_width_chars(78)
        box.pack_start(err, False, False, 0)

        dialog.show_all()
        while dialog.run() == Gtk.ResponseType.OK:
            idx = combo.get_active()
            notation = NOTATION_CHOICES[idx][1] if 0 <= idx < len(NOTATION_CHOICES) else AUTO
            try:
                self.load_position(entry.get_text(), notation)
            except ValueError as e:
                err.set_text(str(e))
                continue
            except Exception as e:  # e.g. the engine process died
                err.set_text(f"Could not import: {e}")
                continue
            break
        dialog.destroy()

    # ----- engine's own moves ------------------------------------------------------
    def maybe_engine_move(self):
        if self.thinking or not self.legal_moves or self.is_human_turn():
            return
        self.trigger_engine_move()

    def make_pump(self, cancel, publish, max_lines):
        pump = InfoPump(
            self.converter, self.start_fen, list(self.moves), self.turn_color(),
            self.fullmove_number(), cancel, publish, max_lines,
        )
        pump.start()
        return pump

    def trigger_engine_move(self):
        self.thinking = True
        self.engine_gen += 1
        gen = self.engine_gen
        cancel = threading.Event()
        self.engine_cancel = cancel
        self.status_label.set_text("Fairy-Stockfish is thinking...")
        movetime_ms = int(self.time_spin.get_value() * 1000)
        moves, start_fen = list(self.moves), self.start_fen
        pump = self.make_pump(cancel, lambda res: GLib.idle_add(self.on_engine_info, gen, res), 1)

        def worker():
            best = None
            try:
                best = self.engine.search(moves, movetime_ms, pump.feed, cancel=cancel, start_fen=start_fen)
            finally:
                pump.close()
            GLib.idle_add(self.finish_engine_move, gen, best)

        threading.Thread(target=worker, daemon=True).start()

    def cancel_engine_move(self):
        """Abandon the engine's search; its answer is discarded."""
        if self.thinking:
            self.engine_gen += 1  # late result from the old search is ignored
            if self.engine_cancel is not None:
                self.engine.request_stop(self.engine_cancel)
            self.engine_cancel = None
            self.thinking = False

    def on_engine_info(self, gen, results):
        if gen == self.engine_gen and self.thinking and results:
            self.eval_label.set_text(format_eval(results[0]))
        return False

    def finish_engine_move(self, gen, bestmove):
        if gen != self.engine_gen:
            return False
        self.thinking = False
        self.engine_cancel = None
        if bestmove and bestmove != "(none)":
            self.moves.append(bestmove)
            self.last_move = bestmove
        self.sync_board()
        self.maybe_engine_move()
        return False

    # ----- background analysis (best-move arrow, engine lines) -----------------------
    def cancel_analysis(self):
        self.analysis_gen += 1  # late results from the old search are ignored
        if self.analysis_cancel is not None:
            self.engine.request_stop(self.analysis_cancel)
            self.analysis_cancel = None
        self.best_move = None
        self.analysis_lines = []

    def maybe_start_analysis(self):
        want_lines = self.lines_chk.get_active()
        if (
            not (want_lines or self.best_chk.get_active())
            or self.thinking
            or not self.legal_moves
            or not self.is_human_turn()
        ):
            self.refresh_lines_panel()
            return
        cancel = threading.Event()
        self.analysis_cancel = cancel
        gen = self.analysis_gen
        moves, start_fen = list(self.moves), self.start_fen
        n_lines = NUM_LINES if want_lines else 1
        pump = self.make_pump(cancel, lambda res: GLib.idle_add(self.on_analysis_lines, gen, res), n_lines)

        def worker():
            try:
                self.engine.search(moves, None, pump.feed, cancel=cancel, multipv=n_lines, start_fen=start_fen)
            finally:
                pump.close()

        threading.Thread(target=worker, daemon=True).start()
        self.refresh_lines_panel()

    def on_analysis_lines(self, gen, results):
        if gen != self.analysis_gen or not results:
            return False
        self.analysis_lines = results
        top = results[0]
        self.best_move = top["pv"][0] if top["pv"] else None
        self.eval_label.set_text(format_eval(top, show_line=not self.lines_chk.get_active()))
        self.refresh_lines_panel()
        self.area.queue_draw()
        return False

    def on_analysis_option_toggled(self, _):
        if self.lines_chk.get_active():
            self.lines_box.show()
        else:
            self.lines_box.hide()
        self.cancel_analysis()
        self.maybe_start_analysis()
        self.area.queue_draw()

    def refresh_lines_panel(self):
        rows = [""] * NUM_LINES
        if self.lines_chk.get_active():
            if self.analysis_lines:
                for i, info in enumerate(self.analysis_lines[:NUM_LINES]):
                    rows[i] = format_line_row(info)
            elif self.analysis_cancel is not None:
                rows[0] = "Analysing…"
            elif self.legal_moves and not self.is_human_turn():
                rows[0] = "(lines are shown on your turn)"
        for lbl, text in zip(self.line_labels, rows):
            lbl.set_markup(f"<tt>{html.escape(text)}</tt>")

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
        if clicked is None or self.thinking or not self.is_human_turn() or not self.legal_moves:
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
        self.maybe_engine_move()

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