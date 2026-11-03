"""Dragonanga engine tester (Fairy-Stockfish).

Engine: the app looks for dragonanga-engine (or stockfish) next to itself, otherwise it asks
for the file. You can also pass the path as an argument or set DRAGONANGA_ENGINE.

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

Engine strength
  * Strength 1-8     how well the engine plays when it moves (1 weakest, 8 full strength).
                     The analysis (Eval / Lines / Suggestion) always runs at full strength.
                     At 8 the engine thinks for the Think Time below; levels 1-7 use short
                     fixed times, like the levels on Lichess.

Analysis (a second engine analyses the position on the board all the time, in every mode)
  * Eval [ ]         bar + score + depth, from White's point of view: +0.3 = White is ahead
  * Lines [ ]        the engine's best lines in designer notation (piece letter + square, x = capture,
                     =F promotion, + check, # mate), in a box beside two spin boxes:
                     Lines (1-5 lines worked out) and Threads (CPU threads used, default 2)
  * Suggestion [ ]   blue arrow for the engine's best move on your turn
  The three boxes only show or hide things; they never restart the engine's calculation. It only
  starts again when the position changes, or when you change Lines or Threads.

Visual Settings (button at the right end of the Eval line; everything changes at once)
  * Pieces            Simple tokens (built in) or any picture set found in the pieces/ folder,
                      with a Dragon beside the list as a preview
  * Board colors      Classic (wood), Green (chess.com), Blue (Lichess) or Custom: two swatches open
                      a colour picker (click or drag, RGB boxes, hex code); a 4-square preview
  * Engine lines      Top (above the Eval line) or Bottom (at the bottom of the window)
  * Light / Dark      the sliding sun / moon switch; it themes every window of the app

Settings (settings.json in your user folder; delete it to start again with the defaults)
  Remembered: piece set, board colors, Light / Dark mode, where the engine lines go,
  Eval / Lines / Suggestion / Move List, number of lines and threads.
  Windows %APPDATA%\\Dragonanga, Linux ~/.config/Dragonanga (or $DRAGONANGA_CONFIG for any file).
  The game itself is never saved: the app always starts a new game.

Move list
  * Move List        tick it to show the game next to the board in designer notation. Click a move
                     to jump to that position. Playing a different move from an earlier position
                     starts a variation (shown in brackets); nothing is ever deleted.
  * Undo Move / Redo Move   step back / forward (against the engine: your move and its reply)
  * Import PGN / Export PGN   below the list; variations are kept

Pieces (chosen in Visual Settings)
  * Picture sets go in the pieces/ folder, e.g. pieces/Handmade/white-soldier.png ... black-minister.png
    (python play_dragonanga.py --check-pieces tells you what was found)

Drawing
  * Right click + drag   arrow (Shift red, Ctrl orange, Alt purple); right click a square = circle
  * Left click           select / move, and clears the drawings
"""
import bisect
import collections
import colorsys
import datetime
import html
import json
import math
import os
import re
import subprocess
import sys
import threading
import cairo
import gi

gi.require_version("Gtk", "3.0")
from gi.repository import Gtk, Gdk, GLib, Pango

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
    "analysis": ({"w", "b"}, "Analysis"),
}

SIDE_WIDTH = 250   # width of the move list panel in pixels
MAX_INDENT = 8     # deepest variation level that is indented further
DEFAULT_LINES = 3  # engine lines calculated / shown to start with
MAX_LINES = 5      # most lines the Lines box can show
DEFAULT_THREADS = 2
MAX_PLIES = 10     # plies shown per line
ANALYSIS_HASH_MB = 128    # memory of the always-on analysis engine
LINES_BOX_HEIGHT = 76     # pixels: the Lines box is about three lines tall, more lines scroll
WINDOW_SIZE = (840, 780)  # wide enough for the toolbar; the move list fits in the space beside the board

# Strength levels 1-8, the same scheme the Lichess / Pychess AI levels use: Fairy-Stockfish's
# "Skill Level" option (it deliberately picks weaker moves) plus a depth cap and a time limit per
# move.   level -> (Skill Level, depth cap or None, milliseconds per move or None = Think Time)
STRENGTH_LEVELS = {
    1: (-9, 5, 50),
    2: (-5, 5, 100),
    3: (-1, 5, 150),
    4: (3, 5, 200),
    5: (7, 5, 300),
    6: (11, 8, 400),
    7: (16, 13, 500),
    8: (20, None, None),   # full strength: Skill Level 20 (off), no depth cap, Think Time
}
DEFAULT_STRENGTH = 8
FULL_SKILL = 20            # Fairy-Stockfish's "Skill Level" when no handicap is wanted


def strength_settings(level, think_ms):
    """Strength level 1-8 and the Think Time (ms) -> (skill_level, depth_cap_or_None, movetime_ms)."""
    level = max(1, min(8, int(level)))
    skill, depth, movetime = STRENGTH_LEVELS[level]
    return skill, depth, (think_ms if movetime is None else min(movetime, think_ms))


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
    """How many plies to keep after 'Undo Move', or None if there is nothing to undo.

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
    cp = mate = None
    if mate_m:
        mate = int(mate_m.group(1)) * sign
        score = f"#{mate}"  # '#3' White mates in 3, '#-3' Black mates in 3
    else:
        cp = int(cp_m.group(1)) * sign
        score = f"{cp / 100.0:+.2f}"
    depth_m = re.search(r"\bdepth\s+(\d+)", line)
    mpv_m = re.search(r"\bmultipv\s+(\d+)", line)
    pv_m = re.search(r"\bpv\s+(.+)$", line)
    return {
        "depth": int(depth_m.group(1)) if depth_m else None,
        "multipv": int(mpv_m.group(1)) if mpv_m else 1,
        "score": score,
        "cp": cp,          # centipawns from White's point of view (None when there is a mate score)
        "mate": mate,      # moves to mate, + = White mates, - = Black mates (None when there is none)
        "pv": pv_m.group(1).split() if pv_m else [],
    }


def format_eval(info):
    depth = info["depth"] if info["depth"] is not None else "?"
    return f"{info['score']} | Depth: {depth}"


def format_eval_short(info):
    """Score for the eval bar: one decimal ('+0.3', '-1.2') or a mate ('#3', '#-3')."""
    if info is None:
        return "--"
    if info.get("mate") is not None:
        return f"#{info['mate']}"
    tenths = int(abs(info["cp"]) / 10.0 + 0.5)          # rounded half up, the same for both signs
    if tenths == 0:
        return "+0.0"                                   # never "-0.0"
    return f"{'-' if info['cp'] < 0 else '+'}{tenths / 10.0:.1f}"


def eval_fraction(info):
    """How much of the eval bar is White's (0 = Black is winning, 1 = White is winning).  The same
    curve Lichess uses for its bar: 50 % at 0.00, ~73 % at +1.00, ~97 % at +10."""
    if info is None:
        return 0.5
    if info.get("mate") is not None:
        return 1.0 if info["mate"] > 0 else 0.0
    return 1.0 / (1.0 + math.exp(-0.00368208 * info["cp"]))


def format_line_row(info):
    depth = info["depth"] if info["depth"] is not None else "?"
    return f"{info['score']:>7}  d{depth:<3} {info.get('text', '')}"


# ----- colours: board colour schemes and the Light / Dark themes ----------------------------------------
HEX_COLOUR = re.compile(r"^#?([0-9a-fA-F]{3}|[0-9a-fA-F]{6})$")


def parse_hex_colour(text):
    """'#RRGGBB' -> (r, g, b) as 0-255 ints, or None.  The '#' and the case are optional, '#abc' works too."""
    match = HEX_COLOUR.match(text.strip()) if isinstance(text, str) else None
    if not match:
        return None
    digits = match.group(1)
    if len(digits) == 3:
        digits = "".join(ch * 2 for ch in digits)
    return int(digits[0:2], 16), int(digits[2:4], 16), int(digits[4:6], 16)


def to_hex(rgb):
    """(r, g, b) as 0-255 -> '#RRGGBB'."""
    return "#%02X%02X%02X" % tuple(max(0, min(255, int(round(v)))) for v in rgb)


def hex_to_unit(text):
    """'#RRGGBB' -> (r, g, b) as 0..1, the way cairo wants them."""
    r, g, b = parse_hex_colour(text)
    return r / 255.0, g / 255.0, b / 255.0


def rgb_to_hsv(rgb):
    """(r, g, b) 0-255 -> (hue, saturation, value), each 0..1."""
    return colorsys.rgb_to_hsv(rgb[0] / 255.0, rgb[1] / 255.0, rgb[2] / 255.0)


def hsv_to_rgb(h, s, v):
    """(hue, saturation, value) 0..1 -> (r, g, b) as 0-255 ints."""
    r, g, b = colorsys.hsv_to_rgb(h, s, v)
    return int(round(r * 255)), int(round(g * 255)), int(round(b * 255))


def relative_luminance(rgb):
    """How bright a colour looks (0 black .. 1 white); rgb is 0..1."""
    def lin(c):
        return c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4
    return 0.2126 * lin(rgb[0]) + 0.7152 * lin(rgb[1]) + 0.0722 * lin(rgb[2])


def contrast_ratio(a, b):
    la, lb = relative_luminance(a), relative_luminance(b)
    return (max(la, lb) + 0.05) / (min(la, lb) + 0.05)


# Board colour schemes: key -> (name, light square, dark square).
#   classic  the wood colours the board always had
#   green    the chess.com board (light #EBECD0, dark #739552)
#   blue     the Lichess "blue" board (light #DEE3E6, dark #8CA2AD)
BOARD_SCHEMES = {
    "classic": ("Classic", "#EDD9B5", "#B58763"),
    "green": ("Green", "#EBECD0", "#739552"),
    "blue": ("Blue", "#DEE3E6", "#8CA2AD"),
}
CUSTOM = "custom"
SCHEME_CHOICES = [(key, entry[0]) for key, entry in BOARD_SCHEMES.items()] + [(CUSTOM, "Custom")]
DEFAULT_BOARD_SCHEME = "classic"


def scheme_hexes(scheme, custom_light=None, custom_dark=None):
    """(light square, dark square) as '#RRGGBB' for a scheme; Custom uses the two given colours."""
    if scheme == CUSTOM:
        return (custom_light or BOARD_SCHEMES[DEFAULT_BOARD_SCHEME][1],
                custom_dark or BOARD_SCHEMES[DEFAULT_BOARD_SCHEME][2])
    entry = BOARD_SCHEMES.get(scheme) or BOARD_SCHEMES[DEFAULT_BOARD_SCHEME]
    return entry[1], entry[2]


def board_colours(scheme, custom_light=None, custom_dark=None):
    """Everything draw_board needs to know about colour (r, g, b as 0..1, alphas where see-through):
    the two squares, the mark on the last move, the selected square, the legal-move dots and the
    coordinate letters.  The marks are drawn over the square, so they work on any colours."""
    light_hex, dark_hex = scheme_hexes(scheme, custom_light, custom_dark)
    light, dark = hex_to_unit(light_hex), hex_to_unit(dark_hex)

    def letters(square, other):          # the other square's colour, unless that is too faint to read
        if contrast_ratio(square, other) >= 2.0:
            return other
        return (0.12, 0.12, 0.12) if relative_luminance(square) > 0.35 else (0.94, 0.94, 0.94)

    if scheme in ("classic", "blue"):    # the Lichess look: a green-yellow wash, green dots
        mark = (155 / 255.0, 199 / 255.0, 0.0, 0.41)
        dot = (0.15, 0.65, 0.25, 0.75)
    else:                                # the chess.com look: a yellow wash, grey dots
        mark = (1.0, 1.0, 0.2, 0.5)
        dot = (0.0, 0.0, 0.0, 0.30) if relative_luminance(dark) > 0.2 else (1.0, 1.0, 1.0, 0.40)
    return {
        "light": light, "dark": dark,
        "mark": mark, "select": (0.98, 0.82, 0.10, 0.70), "dot": dot,
        "letters_on_light": letters(light, dark), "letters_on_dark": letters(dark, light),
    }


CLASSIC_COLOURS = board_colours(DEFAULT_BOARD_SCHEME)

# Light and Dark mode.  "surface" is the colour of the boxes you read from: the move list, the
# engine Lines box, and (in Light mode) the white part of the evaluation bar.
LIGHT_SURFACE = "#FFFFFF"
THEMES = {
    "light": {
        "surface": LIGHT_SURFACE, "text": "#2E3436",
        "bar_white": hex_to_unit(LIGHT_SURFACE), "bar_dark": (0.18, 0.18, 0.18),
        "bar_edge": (0.45, 0.45, 0.45), "bar_mark": (0.5, 0.5, 0.5, 0.9),
        "muted": "#7A7A7A", "current_bg": "#FFE082", "current_fg": "#000000",
    },
    "dark": {
        "surface": "#262626", "text": "#EEEEEC",
        "bar_white": (0.92, 0.92, 0.92), "bar_dark": (0.07, 0.07, 0.07),
        "bar_edge": (0.42, 0.42, 0.42), "bar_mark": (0.5, 0.5, 0.5, 0.9),
        "muted": "#9A9A9A", "current_bg": "#8A6A00", "current_fg": "#FFFFFF",
    },
}
DEFAULT_THEME = "light"


def theme_css(theme):
    """The style sheet that goes on top of GTK's own theme: the reading boxes get the surface colour."""
    return (
        ".dragon-surface, .dragon-surface viewport, .dragon-surface text "
        f"{{ background-color: {theme['surface']}; color: {theme['text']}; }}\n"
        "button.compact { padding: 0px 8px; min-height: 0px; min-width: 0px; }\n"
    ).encode()


_theme_provider = None
_dark_titlebars = False


def apply_gtk_theme(name):
    """Switch the whole app (every window and dialog) to Light or Dark mode and return the theme.
    GTK's built-in Adwaita theme is used on every system, because it has a dark variant."""
    global _theme_provider, _dark_titlebars
    theme = THEMES.get(name) or THEMES[DEFAULT_THEME]
    _dark_titlebars = theme is THEMES["dark"]
    try:
        settings = Gtk.Settings.get_default()
        if settings is not None:
            settings.set_property("gtk-theme-name", "Adwaita")
            settings.set_property("gtk-application-prefer-dark-theme", _dark_titlebars)
    except Exception:
        pass
    try:
        screen = Gdk.Screen.get_default()
        if screen is not None:
            if _theme_provider is None:
                _theme_provider = Gtk.CssProvider()
                Gtk.StyleContext.add_provider_for_screen(
                    screen, _theme_provider, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
            _theme_provider.load_from_data(theme_css(theme))
    except Exception:
        pass            # cosmetic: without the style sheet the boxes simply keep the theme's own colours
    return theme


def set_titlebar_dark(window):
    """Windows draws the title bar itself, so GTK's theme does not reach it: ask Windows for a dark
    one (or a light one) to match.  Does nothing on other systems, or if anything is missing."""
    if os.name != "nt":
        return
    try:
        import ctypes
        gdk_window = window.get_window()
        if gdk_window is None:
            return
        get_pointer = ctypes.pythonapi.PyCapsule_GetPointer
        get_pointer.restype = ctypes.c_void_p
        get_pointer.argtypes = [ctypes.py_object, ctypes.c_char_p]
        gdk = ctypes.CDLL("libgdk-3-0.dll")
        gdk.gdk_win32_window_get_handle.restype = ctypes.c_void_p
        gdk.gdk_win32_window_get_handle.argtypes = [ctypes.c_void_p]
        hwnd = gdk.gdk_win32_window_get_handle(get_pointer(gdk_window.__gpointer__, None))
        if not hwnd:
            return
        value = ctypes.c_int(1 if _dark_titlebars else 0)
        for attribute in (20, 19):       # DWMWA_USE_IMMERSIVE_DARK_MODE (19 before Windows 10 20H1)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                ctypes.c_void_p(hwnd), attribute, ctypes.byref(value), ctypes.sizeof(value))
    except Exception:
        pass


def watch_titlebar(window):
    """Give a window the right title bar each time it appears (Windows only)."""
    if os.name == "nt":
        window.connect("map", lambda *_: set_titlebar_dark(window))


# ----- settings file ---------------------------------------------------------
LINES_POSITIONS = ("top", "bottom")
DEFAULT_LINES_POSITION = "top"

SETTINGS_DEFAULTS = {
    "piece_set": None,          # name of the piece set (None = the default one)
    "show_eval": True,
    "show_lines": False,
    "show_suggestion": False,
    "show_move_list": False,
    "lines": DEFAULT_LINES,
    "threads": DEFAULT_THREADS,
    "board_scheme": DEFAULT_BOARD_SCHEME,
    "custom_light": None,       # '#RRGGBB' of the Custom board, None = not chosen yet
    "custom_dark": None,
    "lines_position": DEFAULT_LINES_POSITION,
    "theme": DEFAULT_THEME,
}


def max_threads():
    """Most threads the Threads box offers: one per logical CPU of this computer (at most 32)."""
    return max(1, min(32, os.cpu_count() or 4))


def settings_path():
    """Where the settings live: DRAGONANGA_CONFIG if set, else the usual per-user config folder."""
    override = os.environ.get("DRAGONANGA_CONFIG")
    if override:
        return override
    if os.name == "nt":
        base = os.environ.get("APPDATA") or os.path.join(os.path.expanduser("~"), "AppData", "Roaming")
    elif sys.platform == "darwin":
        base = os.path.join(os.path.expanduser("~"), "Library", "Application Support")
    else:
        base = os.environ.get("XDG_CONFIG_HOME") or os.path.join(os.path.expanduser("~"), ".config")
    return os.path.join(base, "Dragonanga", "settings.json")


def sanitize_settings(raw):
    """Settings read from a file -> a complete dict with every value valid (bad or missing ones fall
    back to the defaults, so a damaged or hand-edited file can never break the start-up)."""
    out = dict(SETTINGS_DEFAULTS)
    if not isinstance(raw, dict):
        return out
    for key in ("show_eval", "show_lines", "show_suggestion", "show_move_list"):
        if isinstance(raw.get(key), bool):
            out[key] = raw[key]
    for key, low, high in (("lines", 1, MAX_LINES), ("threads", 1, max_threads())):
        value = raw.get(key)
        if isinstance(value, int) and not isinstance(value, bool):
            out[key] = max(low, min(high, value))
    if isinstance(raw.get("piece_set"), str):
        out["piece_set"] = raw["piece_set"]
    out["threads"] = min(out["threads"], max_threads())
    schemes = [key for key, _name in SCHEME_CHOICES]
    for key, allowed in (("board_scheme", schemes), ("lines_position", LINES_POSITIONS), ("theme", list(THEMES))):
        value = raw.get(key)
        if isinstance(value, str) and value in allowed:     # (a list or number in the file must not crash this)
            out[key] = value
    for key in ("custom_light", "custom_dark"):
        rgb = parse_hex_colour(raw.get(key))
        out[key] = to_hex(rgb) if rgb else None
    return out


def load_settings(path=None):
    try:
        with open(path or settings_path(), encoding="utf-8") as f:
            return sanitize_settings(json.load(f))
    except (OSError, ValueError):
        return sanitize_settings(None)       # no file yet, or an unreadable one: defaults


def save_settings(values, path=None):
    """Write the settings file (through a temporary file, so a crash cannot leave half a file).
    Returns False if it could not be written; the app carries on either way."""
    path = path or settings_path()
    try:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(values, f, indent=2, sort_keys=True)
            f.write("\n")
        os.replace(tmp, path)
        return True
    except OSError:
        return False


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


def game_outcome(fen, in_check, prev_fen=None):
    """How a position in which the side to move has no legal moves ended (engine FEN letters).

    Returns (kind, winner): kind is 'draw', 'baremate', 'checkmate' or 'stalemate'; winner is 'w',
    'b' or None for a draw.

    Dragonanga rules: checkmate loses; stalemate WINS for the stalemated side; baremate means a lone
    Queen Fairy that makes a quiet (non-capturing) move loses at once while the opponent still has other
    pieces (and it is a draw if the opponent is a lone Queen Fairy too). The engine ends the game right
    after that move, so the side to move 'has no moves' then.
    prev_fen is the position before the last move (None at a loaded position, where no move has been
    played yet)."""
    parts = fen.split()
    stm = parts[1] if len(parts) > 1 else "w"
    mover = "b" if stm == "w" else "w"

    def pieces(side):
        return [ch.upper() for ch in parts[0] if ch.isalpha() and ch.isupper() == (side == "w")]

    def was_capture(before, after):
        """Did the last move capture? One fewer piece on the board than before."""
        count = lambda f: sum(ch.isalpha() for ch in f.split()[0])
        return count(before) > count(after)

    mover_bare = pieces(mover) == ["K"]             # engine letter K = Queen Fairy (royal)
    stm_not_bare = any(ch != "K" for ch in pieces(stm))
    quiet = bool(prev_fen) and not was_capture(prev_fen, fen)
    if mover_bare and not stm_not_bare and quiet:
        return "draw", None
    if mover_bare and stm_not_bare and quiet:
        return "baremate", stm
    if in_check:
        return "checkmate", mover
    return "stalemate", stm


def game_over_text(fen, in_check, prev_fen=None):
    """Message for a position in which the side to move has no legal moves (engine FEN letters)."""
    kind, winner = game_outcome(fen, in_check, prev_fen)
    name = {"w": "White", "b": "Black"}
    stm = fen.split()[1] if len(fen.split()) > 1 else "w"
    mover = other_side(stm)
    if kind == "draw":
        return "Game Over — Draw! Both sides are down to a lone Queen Fairy."
    if kind == "baremate":
        return (f"Game Over — Baremate! {name[mover]}'s lone Queen Fairy made a quiet move. "
                f"{name[winner]} wins.")
    if kind == "checkmate":
        return f"Game Over — Checkmate! {name[winner]} wins."
    return f"Game Over — Stalemate! {name[stm]} has no moves and wins."


def pgn_result(fen, in_check, prev_fen=None):
    """PGN result string for a finished position: '1-0', '0-1' or '1/2-1/2'."""
    return {"w": "1-0", "b": "0-1", None: "1/2-1/2"}[game_outcome(fen, in_check, prev_fen)[1]]


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


# ---------------------------------------------------------------------------
# Game tree: the move list with variations
#
# Every move is a Node that points straight at its parent and its children (no id lookups needed).
# children[0] is the main continuation, the other children are variations.  The current position is
# just a pointer to one node; the moves from the start are found by walking up the parents.  Undo,
# redo and jumping only move that pointer, so nothing is ever deleted (a move you take back stays
# in the list as a variation as soon as you play something else).
# ---------------------------------------------------------------------------
class Node:
    __slots__ = ("id", "move", "san", "fen", "parent", "children", "ply", "redo")

    def __init__(self, node_id, move, san, fen, parent):
        self.id = node_id          # unique number, used by the move list to find the node again
        self.move = move           # UCI move that led here (None for the start position)
        self.san = san             # the same move in designer notation, e.g. 'Gc3+'
        self.fen = fen             # engine FEN after the move (None if not known)
        self.parent = parent
        self.children = []
        self.ply = parent.ply + 1 if parent else 0
        self.redo = None           # the child Redo should follow (the one visited last)

    def child_for(self, move):
        for child in self.children:
            if child.move == move:
                return child
        return None


class GameTree:
    def __init__(self, start_fen=None):
        self.start_fen = start_fen                         # None = the normal start position
        parts = start_fen.split() if start_fen else []
        self.start_stm = parts[1] if len(parts) > 1 else "w"
        try:
            self.start_fullmove = max(1, int(parts[5]))
        except (IndexError, ValueError):
            self.start_fullmove = 1
        self.root = Node(0, None, None, start_fen, None)
        self.nodes = {0: self.root}
        self._next_id = 1

    def add(self, parent, move, san=None, fen=None):
        """The child of `parent` that plays `move`; it is created unless it already exists."""
        child = parent.child_for(move)
        if child is None:
            child = Node(self._next_id, move, san or move, fen, parent)
            self._next_id += 1
            parent.children.append(child)
            self.nodes[child.id] = child
        return child

    def moves(self, node):
        """UCI moves from the start position to `node`."""
        out = []
        while node.parent is not None:
            out.append(node.move)
            node = node.parent
        out.reverse()
        return out

    def visit(self, node):
        """Remember the way to `node` so that Redo walks back down the same line."""
        while node.parent is not None:
            node.parent.redo = node
            node = node.parent

    def redo_child(self, node):
        if node.redo is not None and node.redo in node.children:
            return node.redo
        return node.children[0] if node.children else None

    def main_end(self):
        node = self.root
        while node.children:
            node = node.children[0]
        return node

    def ancestor(self, node, ply):
        while node.ply > ply:
            node = node.parent
        return node

    def stm_after(self, node):
        """Side to move in the position after `node`."""
        return self.start_stm if node.ply % 2 == 0 else other_side(self.start_stm)

    def mover(self, node):
        """Side that played the move `node`."""
        return other_side(self.stm_after(node))

    def fullmove(self, node):
        """Full-move number of the move `node` (1 for the first move of a normal game)."""
        return self.start_fullmove + (node.ply - 1 + (0 if self.start_stm == "w" else 1)) // 2


# ----- the move list text -----------------------------------------------------
Seg = collections.namedtuple("Seg", "text node style level")   # style: num, move, paren or plain


def layout_move_list(tree):
    """The move list as a list of Seg pieces (text, the node it stands for, style, indent level).

    Main line in two columns, variations indented below the move they replace:
        1.  Ga3     Ga6
            (1. Gb3 Gb6 2. Ga4
              (2. Gc3))
        2.  Gb4     Gb6"""
    segs = []

    def add(text, node=None, style="plain", level=0):
        if text:
            segs.append(Seg(text, node, style, level))

    def at_line_start():
        return not segs or segs[-1].text.endswith("\n")

    def newline(level=0):
        if not at_line_start():
            add("\n", None, "plain", level)

    def number(num, dots):
        text = f"{num}{dots}"
        return text + " " * max(1, 4 - len(text))

    def variation(first, level):
        newline(level)
        add("(", None, "paren", level)
        node, need_num = first, True

        def tok(text, tok_node=None, style="plain"):
            if segs and segs[-1].text[-1] not in "(\n":
                add(" ", None, "plain", level)
            add(text, tok_node, style, level)

        while node:
            num = tree.fullmove(node)
            if tree.mover(node) == "w":
                tok(f"{num}.", None, "num")
            elif need_num:
                tok(f"{num}...", None, "num")
            tok(node.san, node, "move")
            need_num = False
            parent = node.parent
            alts = parent.children[1:] if node is parent.children[0] else []
            for alt in alts:
                variation(alt, level + 1)
            if alts and node.children:
                newline(level)
                need_num = True
            node = node.children[0] if node.children else None
        add(")", None, "paren", level)

    node, row_white = tree.root, None      # row_white: the White move a row currently ends with
    while node.children:
        child = node.children[0]
        num = tree.fullmove(child)
        if tree.mover(child) == "w":
            newline()
            add(number(num, "."), None, "num")
            add(child.san, child, "move")
            row_white = child.san
        elif row_white is not None:
            add(" " * max(2, 8 - len(row_white)), None, "plain")
            add(child.san, child, "move")
            row_white = None
        else:
            newline()
            add(number(num, "..."), None, "num")
            add(child.san, child, "move")
        alts = node.children[1:]
        for alt in alts:
            variation(alt, 1)
        if alts:
            newline()
            row_white = None
        node = child
    return segs


# ----- PGN ----------------------------------------------------------------------------
PGN_RESULTS = ("1-0", "0-1", "1/2-1/2", "*")


def pgn_movetext(tree):
    """Move text of a PGN: '1. Ga3 Ga6 (1... Gb6 2. Ga4) 2. Gb4', variations in parentheses."""
    def line(first):
        tokens, node, force = [], first, True
        while node:
            num = tree.fullmove(node)
            if tree.mover(node) == "w":
                tokens.append(f"{num}.")
            elif force:
                tokens.append(f"{num}...")
            tokens.append(node.san)
            force = False
            parent = node.parent
            alts = parent.children[1:] if node is parent.children[0] else []
            for alt in alts:
                sub = line(alt)
                sub[0] = "(" + sub[0]
                sub[-1] += ")"
                tokens.extend(sub)
            if alts:
                force = True
            node = node.children[0] if node.children else None
        return tokens
    return line(tree.root.children[0]) if tree.root.children else []


def tree_to_pgn(tree, result="*", date=None):
    """The whole game as PGN text.  Piece letters are the designer letters (S G E H D Q K F M)."""
    tags = [
        ("Event", "Dragonanga Engine Tester game"), ("Site", "?"),
        ("Date", date or datetime.date.today().strftime("%Y.%m.%d")), ("Round", "-"),
        ("White", "?"), ("Black", "?"), ("Result", result), ("Variant", "Dragonanga"),
    ]
    if tree.start_fen:
        tags += [("SetUp", "1"), ("FEN", engine_fen_to_designer(tree.start_fen))]
    out = ['[%s "%s"]' % (k, re.sub(r'(["\\])', r"\\\1", v)) for k, v in tags]   # escape " and \
    out.append("")
    row = ""
    for token in pgn_movetext(tree) + [result]:     # wrap at 80 columns
        if row and len(row) + 1 + len(token) > 80:
            out.append(row)
            row = token
        else:
            row = f"{row} {token}" if row else token
    out.append(row)
    return "\n".join(out) + "\n"


PGN_TAG = re.compile(r'^\s*\[(\w+)\s+"((?:[^"\\]|\\.)*)"\s*\]\s*$')
PGN_TOKEN = re.compile(r"\(|\)|\{[^}]*\}|;[^\n]*|\$\d+|\d+\.+|1-0|0-1|1/2-1/2|\*|[^\s(){};$]+")


def split_pgn(text):
    """First game of a PGN text -> (tag dict, movetext)."""
    tags, body, in_body = {}, [], False
    for raw in text.replace("\ufeff", "").splitlines():
        line = raw.strip()
        if line.startswith("%"):
            continue
        match = PGN_TAG.match(raw)
        if match and not in_body:
            tags[match.group(1)] = re.sub(r'\\(["\\])', r"\1", match.group(2))   # undo \" and \\
        elif match and in_body and body:
            break                                    # the tags of the next game
        elif line:
            in_body = True
            body.append(raw)
    return tags, "\n".join(body)


def pgn_to_tree(text, converter):
    """Read the first game of a PGN text into a GameTree.  Raises ValueError with a readable message
    if the text has no moves, a bad FEN tag, an illegal move or unbalanced parentheses."""
    tags, body = split_pgn(text)
    start_fen = None
    if tags.get("FEN") and tags.get("SetUp", "1") != "0":
        try:
            start_fen, _ = parse_import_fen(tags["FEN"])
        except ValueError as e:
            raise ValueError(f"The FEN tag in the PGN is not usable: {e}")
    tree = GameTree(start_fen)
    cur, stack, played = tree.root, [], 0
    for match in PGN_TOKEN.finditer(body):
        tok = match.group(0)
        if tok == "(":
            if cur.parent is None:
                raise ValueError("A variation '(' appears before the first move.")
            stack.append(cur)
            cur = cur.parent
        elif tok == ")":
            if not stack:
                raise ValueError("Unbalanced ')' in the move text.")
            cur = stack.pop()
        elif tok in PGN_RESULTS:
            if not stack:
                break
        elif tok[0] in "{;$" or re.match(r"^\d+\.+$", tok):
            continue                                  # comment, NAG or move number
        else:
            before = tree.moves(cur)
            try:
                uci = converter.parse_san(start_fen, before, tok)
            except ValueError:
                raise ValueError(f"The move {tok!r} (ply {len(before) + 1}) is not legal in that position.")
            san, fen = converter.san_move(start_fen, before, uci)
            cur = tree.add(cur, uci, san, fen)
            played += 1
    if stack:
        raise ValueError("A variation '(' is never closed.")
    if not played:
        raise ValueError("No moves found in the PGN.")
    return tree


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


def draw_piece(cr, piece, x, y, sq, images=None):
    """Draw one piece (engine letter, upper case = White) in the square whose top-left corner is (x, y):
    a picture from the chosen set, or the built-in token."""
    picture = images.get(piece, sq * PIECE_IMAGE_SCALE) if (piece and images) else None
    if picture is not None:
        side = picture.get_width()
        cr.set_source_surface(picture, x + (sq - side) / 2.0, y + (sq - side) / 2.0)
        cr.paint()
    elif piece:
        is_white = piece.isupper()
        cx, cy = x + sq / 2.0, y + sq / 2.0
        cr.select_font_face("Sans", cairo.FONT_SLANT_NORMAL, cairo.FONT_WEIGHT_BOLD)

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


def draw_board(cr, size, grid, flipped, selected_sq, targets, last_move, notes, best_move, images=None,
               colours=None):
    colours = colours or CLASSIC_COLOURS
    sq = size / 8.0
    cr.select_font_face("Sans", cairo.FONT_SLANT_NORMAL, cairo.FONT_WEIGHT_BOLD)

    for r in range(8):
        for c in range(8):
            name = screen_to_sq(r, c, flipped)
            br, bc = (7 - r, 7 - c) if flipped else (r, c)  # index into the FEN grid
            light = (r + c) % 2 == 0
            cr.set_source_rgb(*(colours["light"] if light else colours["dark"]))
            cr.rectangle(c * sq, r * sq, sq, sq)
            cr.fill()
            if name == selected_sq:                          # a wash over the square: works on any colours
                cr.set_source_rgba(*colours["select"])
            elif last_move and name in (last_move[:2], last_move[2:4]):
                cr.set_source_rgba(*colours["mark"])
            if name == selected_sq or (last_move and name in (last_move[:2], last_move[2:4])):
                cr.rectangle(c * sq, r * sq, sq, sq)
                cr.fill()

            # Legal move target dot
            if name in targets:
                cr.set_source_rgba(*colours["dot"])
                cr.arc((c + 0.5) * sq, (r + 0.5) * sq, sq * 0.18, 0, 6.283)
                cr.fill()

            # Coordinate labels (follow the board orientation)
            cr.set_source_rgb(*colours["letters_on_light" if light else "letters_on_dark"])
            if c == 0:
                cr.set_font_size(sq * 0.16)
                cr.move_to(c * sq + 3, r * sq + sq * 0.20)
                cr.show_text(name[1])
            if r == 7:
                cr.set_font_size(sq * 0.16)
                cr.move_to((c + 1) * sq - sq * 0.20, (r + 1) * sq - 4)
                cr.show_text(name[0])

            # Piece: a picture from the chosen set, or the built-in token
            draw_piece(cr, grid[br][bc], c * sq, r * sq, sq, images)

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
def draw_eval_bar(cr, width, height, white_share, theme=None):
    """The evaluation bar: White's share is the light part on the left, Black's the dark part."""
    theme = theme or THEMES[DEFAULT_THEME]
    r = min(height / 2.0, 8.0)
    x, y, w, h = 0.5, 0.5, width - 1.0, height - 1.0

    def outline():
        cr.new_sub_path()
        cr.arc(x + w - r, y + r, r, -math.pi / 2, 0)
        cr.arc(x + w - r, y + h - r, r, 0, math.pi / 2)
        cr.arc(x + r, y + h - r, r, math.pi / 2, math.pi)
        cr.arc(x + r, y + r, r, math.pi, 3 * math.pi / 2)
        cr.close_path()

    cr.save()
    outline()
    cr.clip()
    cr.set_source_rgb(*theme["bar_dark"])
    cr.paint()
    cr.set_source_rgb(*theme["bar_white"])
    cr.rectangle(0, 0, width * max(0.0, min(1.0, white_share)), height)
    cr.fill()
    cr.set_source_rgba(*theme["bar_mark"])           # thin mark at 0.00
    cr.rectangle(width / 2.0 - 0.5, 0, 1, height)
    cr.fill()
    cr.restore()
    outline()
    cr.set_source_rgb(*theme["bar_edge"])
    cr.set_line_width(1)
    cr.stroke()


# ----- small pictures used by the Visual Settings window ------------------------------------------
def rounded_rect(cr, x, y, w, h, r):
    r = max(0.0, min(r, w / 2.0, h / 2.0))
    cr.new_sub_path()
    cr.arc(x + w - r, y + r, r, -math.pi / 2, 0)
    cr.arc(x + w - r, y + h - r, r, 0, math.pi / 2)
    cr.arc(x + r, y + h - r, r, math.pi / 2, math.pi)
    cr.arc(x + r, y + r, r, math.pi, 3 * math.pi / 2)
    cr.close_path()


def draw_swatch(cr, width, height, rgb):
    """A colour box with a thin edge (rgb 0..1); the clickable boxes of the Custom board colours."""
    rounded_rect(cr, 0.5, 0.5, width - 1, height - 1, 4)
    cr.set_source_rgb(*rgb)
    cr.fill_preserve()
    cr.set_source_rgba(0.0, 0.0, 0.0, 0.45)
    cr.set_line_width(1)
    cr.stroke()


def draw_checker(cr, size, light, dark):
    """Four squares, light and dark like the corner of a board: the board colour preview."""
    half = size / 2.0
    for row in range(2):
        for col in range(2):
            cr.set_source_rgb(*(light if (row + col) % 2 == 0 else dark))
            cr.rectangle(col * half, row * half, half, half)
            cr.fill()
    rounded_rect(cr, 0.5, 0.5, size - 1, size - 1, 3)
    cr.set_source_rgba(0.0, 0.0, 0.0, 0.45)
    cr.set_line_width(1)
    cr.stroke()


def draw_piece_preview(cr, size, colours, images=None, piece="D"):
    """A White Dragon on one dark square of the chosen board colours, drawn with the chosen pieces."""
    rounded_rect(cr, 0.5, 0.5, size - 1, size - 1, 4)
    cr.set_source_rgb(*colours["dark"])
    cr.fill_preserve()
    cr.set_source_rgba(0.0, 0.0, 0.0, 0.45)
    cr.set_line_width(1)
    cr.stroke()
    draw_piece(cr, piece.upper(), 0, 0, size, images)


def draw_sv_square(cr, width, height, hue, sat, val):
    """The colour picker's square: saturation grows to the right, brightness upwards."""
    cr.set_source_rgb(*colorsys.hsv_to_rgb(hue, 1.0, 1.0))
    cr.rectangle(0, 0, width, height)
    cr.fill()
    across = cairo.LinearGradient(0, 0, width, 0)
    across.add_color_stop_rgba(0.0, 1, 1, 1, 1)
    across.add_color_stop_rgba(1.0, 1, 1, 1, 0)
    cr.set_source(across)
    cr.rectangle(0, 0, width, height)
    cr.fill()
    down = cairo.LinearGradient(0, 0, 0, height)
    down.add_color_stop_rgba(0.0, 0, 0, 0, 0)
    down.add_color_stop_rgba(1.0, 0, 0, 0, 1)
    cr.set_source(down)
    cr.rectangle(0, 0, width, height)
    cr.fill()
    cx, cy = sat * width, (1.0 - val) * height          # the ring that marks the chosen colour
    cr.set_line_width(3.0)
    cr.set_source_rgba(0, 0, 0, 0.6)
    cr.new_sub_path()
    cr.arc(cx, cy, 6.0, 0, 6.283185307)
    cr.stroke()
    cr.set_line_width(1.5)
    cr.set_source_rgb(1, 1, 1)
    cr.new_sub_path()
    cr.arc(cx, cy, 6.0, 0, 6.283185307)
    cr.stroke()


def draw_hue_strip(cr, width, height, hue):
    """The rainbow bar under the square, with a handle at the chosen hue."""
    rainbow = cairo.LinearGradient(0, 0, width, 0)
    for i in range(7):
        rainbow.add_color_stop_rgb(i / 6.0, *colorsys.hsv_to_rgb(i / 6.0 if i < 6 else 0.0, 1.0, 1.0))
    cr.set_source(rainbow)
    cr.rectangle(0, 0, width, height)
    cr.fill()
    x = max(2.0, min(width - 2.0, hue * width))
    cr.set_source_rgba(0, 0, 0, 0.6)
    cr.rectangle(x - 3.5, 0, 7, height)
    cr.fill()
    cr.set_source_rgb(1, 1, 1)
    cr.rectangle(x - 2, 1, 4, height - 2)
    cr.fill()


def _mix(a, b, t):
    return tuple(a[i] + (b[i] - a[i]) * t for i in range(len(a)))


def draw_moon(cr, cx, cy, r, colour, cut_colour):
    """A crescent: a disc with a second disc in the background colour taken out of it."""
    cr.set_source_rgb(*colour)
    cr.new_sub_path()
    cr.arc(cx, cy, r, 0, 6.283185307)
    cr.fill()
    cr.set_source_rgb(*cut_colour)
    cr.new_sub_path()
    cr.arc(cx + r * 0.55, cy - r * 0.35, r * 0.82, 0, 6.283185307)
    cr.fill()


def draw_sun(cr, cx, cy, r, colour):
    cr.set_source_rgb(*colour)
    cr.new_sub_path()
    cr.arc(cx, cy, r * 0.55, 0, 6.283185307)
    cr.fill()
    cr.set_line_width(max(1.2, r * 0.2))
    for i in range(8):
        a = i * math.pi / 4
        cr.move_to(cx + math.cos(a) * r * 0.8, cy + math.sin(a) * r * 0.8)
        cr.line_to(cx + math.cos(a) * r * 1.15, cy + math.sin(a) * r * 1.15)
        cr.stroke()


def draw_theme_switch(cr, width, height, pos):
    """The Light / Dark switch.  pos 0 = Dark (the knob on the moon, left), 1 = Light (the sun, right);
    values in between are the knob sliding."""
    night, day = (0.16, 0.20, 0.31), (0.58, 0.80, 0.94)
    track = _mix(night, day, pos)
    rounded_rect(cr, 0.5, 0.5, width - 1, height - 1, (height - 1) / 2.0)
    cr.set_source_rgb(*track)
    cr.fill_preserve()
    cr.set_source_rgba(0.0, 0.0, 0.0, 0.45)
    cr.set_line_width(1)
    cr.stroke()

    margin = height / 2.0
    left, right = margin, width - margin
    icon = height * 0.24
    draw_moon(cr, left, height / 2.0, icon, _mix((0.95, 0.95, 0.85), (0.30, 0.36, 0.52), pos), track)
    draw_sun(cr, right, height / 2.0, icon, _mix((1.0, 0.85, 0.35), (0.98, 0.62, 0.10), pos))

    knob = _mix((0.88, 0.90, 0.95), (1.0, 1.0, 1.0), pos)
    kx = left + (right - left) * pos
    cr.set_source_rgba(0.0, 0.0, 0.0, 0.25)                    # a soft shadow
    cr.new_sub_path()
    cr.arc(kx, height / 2.0 + 1.0, height * 0.40, 0, 6.283185307)
    cr.fill()
    cr.set_source_rgb(*knob)
    cr.new_sub_path()
    cr.arc(kx, height / 2.0, height * 0.40, 0, 6.283185307)
    cr.fill()
    if pos < 0.5:                                              # the knob carries the mode's picture
        draw_moon(cr, kx, height / 2.0, icon, (0.16, 0.20, 0.31), knob)
    else:
        draw_sun(cr, kx, height / 2.0, icon, (0.98, 0.62, 0.10))


class UCIEngine:
    def __init__(self, exe_path):
        self.proc = subprocess.Popen(
            [exe_path],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            universal_newlines=True,
            bufsize=1,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),  # Windows: no black console flashing up
        )
        self.lock = threading.Lock()        # one conversation with the engine at a time
        self._wlock = threading.Lock()      # keeps single commands from interleaving
        self._stop_lock = threading.Lock()  # guards _active_cancel
        self._active_cancel = None          # cancel token of the search that is running now
        self.sent_options = {}              # options set through search(options=...), to send changes only
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
        try:
            self.proc.stdin.close()      # nothing left to flush into the dead pipe
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

    def search(self, moves, movetime_ms, info_callback, cancel=None, multipv=1, start_fen=None,
               skill=FULL_SKILL, depth=None, options=None):
        """Run an engine search and return bestmove.

        movetime_ms=None means 'go infinite' (background analysis); it only ends
        when request_stop(cancel) is called.  If `cancel` is already set by the
        time this search gets its turn, nothing is run.
        skill / depth handicap the search (see STRENGTH_LEVELS); every search sets the skill
        explicitly, so analysis always runs at full strength.
        options: extra engine options ({"Threads": 2, "Hash": 128}); an option is only sent when its
        value is different from the last one sent, because changing Threads / Hash is expensive.
        """
        with self.lock:
            if cancel is not None and cancel.is_set():
                return None
            changed = False
            for name, value in (options or {}).items():
                if self.sent_options.get(name) != value:
                    self.send(f"setoption name {name} value {value}")
                    self.sent_options[name] = value
                    changed = True
            if changed:
                self.wait_ready()
            self.send(f"setoption name MultiPV value {multipv}")
            self.send(f"setoption name Skill Level value {skill}")
            self.send(position_cmd(start_fen, moves))
            go = "go infinite" if movetime_ms is None else f"go movetime {movetime_ms}"
            if depth and movetime_ms is not None:
                go += f" depth {depth}"
            self.send(go)
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

    def san_move(self, start_fen, moves, uci):
        """Designer notation of `uci` played after `moves`, with + / # marks -> (san, fen after)."""
        fen, legal, _ = self.state(start_fen, moves)
        nfen, nlegal, nchk = self.state(start_fen, list(moves) + [uci])
        san = designer_move(fen_to_board(fen), legal, uci, check=nchk, mate=nchk and not nlegal)
        return san, nfen

    def parse_san(self, start_fen, moves, token):
        """UCI move for a designer-notation token ('Gc3', 'Exd4+', ...) in the position after `moves`.
        Check marks and !? are ignored; plain engine moves ('c2c3') are accepted too."""
        fen, legal, _ = self.state(start_fen, moves)
        board = fen_to_board(fen)
        clean = re.sub(r"[+#!?]+$", "", token)
        table = {designer_move(board, legal, m): m for m in legal}
        if clean in table:
            return table[clean]
        loose = [m for san, m in table.items() if san.lower() == clean.lower()]
        if len(loose) == 1:
            return loose[0]
        if clean in legal:
            return clean
        raise ValueError(f"{token!r} is not a legal move here")

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

    def __init__(self, converter, start_fen, moves, stm, fullmove, cancel, publish, max_lines, interval=0.15,
                 need_text=lambda: True):
        self.converter, self.start_fen, self.moves = converter, start_fen, moves
        self.need_text = need_text      # False while the lines are hidden: only scores and moves are needed
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
                text = self._text(info) if self.need_text() else ""
                if text is None:
                    return
                results.append(dict(info, text=text))
            if results:
                self.publish(results)
            self.done.wait(self.interval)


class Analyzer:
    """Keeps one engine process analysing the position on the board the whole time ("go infinite"),
    whatever the mode and whatever is shown, so the evaluation is always the same and always live.

    * It only restarts when the POSITION changes, or the number of lines / threads is changed.
      Showing or hiding the eval, lines or suggestion, switching sides and so on never touch it.
    * It is a separate process from the one that plays the moves, so playing never interrupts it.
    * Results go to publish(generation, results); the window ignores results of an old generation."""

    def __init__(self, engine_path, converter, publish):
        self.engine = UCIEngine(engine_path)
        self.converter, self.publish = converter, publish
        self.key = None              # (start_fen, moves, lines, threads) being analysed now
        self.cancel = None
        self.pump = None
        self.gen = 0                 # grows with every restart / stop
        self.want_text = False       # True while the Lines box is visible (notation is only built then)

    def analyse(self, start_fen, moves, stm, fullmove, lines, threads, fresh=False):
        """Point the analysis at this position.  Returns True if a new search was started and False if
        the engine was already analysing exactly this (then nothing is touched).  fresh=True also
        clears the engine's memory first (a new game)."""
        key = (start_fen, tuple(moves), lines, threads)
        if key == self.key and self.cancel is not None and not fresh:
            return False
        self._stop_search()
        self.key = key
        self.gen += 1
        gen = self.gen
        cancel = threading.Event()
        self.cancel = cancel
        pump = InfoPump(self.converter, start_fen, list(moves), stm, fullmove, cancel,
                        lambda results: self.publish(gen, results), lines, need_text=lambda: self.want_text)
        self.pump = pump
        pump.start()
        moves = list(moves)

        def worker():
            try:
                if fresh and not cancel.is_set():
                    self.engine.new_game()
                self.engine.search(moves, None, pump.feed, cancel=cancel, multipv=lines, start_fen=start_fen,
                                   options={"Threads": threads, "Hash": ANALYSIS_HASH_MB})
            except (OSError, ValueError):
                pass                      # the engine process is gone (the window is closing)
            finally:
                pump.close()

        threading.Thread(target=worker, daemon=True).start()
        return True

    def nudge(self):
        """Publish the latest results again soon (used when the Lines box is switched on)."""
        if self.pump is not None:
            self.pump.wake.set()

    def _stop_search(self):
        if self.cancel is not None:
            self.engine.request_stop(self.cancel)
            self.cancel = None

    def stop(self):
        """Stop analysing (game over)."""
        self._stop_search()
        self.key = None
        self.gen += 1

    def close(self):
        self.stop()
        self.engine.close()


# ---------------------------------------------------------------------------
# Window
# ---------------------------------------------------------------------------
class DragonangaWindow(Gtk.Window):
    def __init__(self, engine_path):
        super().__init__(title="Dragonanga Engine Tester (Fairy-Stockfish)")
        self.prefs_path = settings_path()
        self.prefs = load_settings(self.prefs_path)
        self.loading_prefs = True              # nothing is saved while the saved values are applied
        self.theme_name = self.prefs["theme"]
        self.theme = apply_gtk_theme(self.theme_name)     # before any widget exists, so nothing flashes
        self.board_scheme = self.prefs["board_scheme"]
        self.custom_light = self.prefs["custom_light"]    # '#RRGGBB' or None (not chosen yet)
        self.custom_dark = self.prefs["custom_dark"]
        self.board_colours = board_colours(self.board_scheme, self.custom_light, self.custom_dark)
        self.lines_position = self.prefs["lines_position"]
        self.visual_win = None                 # the Visual Settings window while it is open
        watch_titlebar(self)
        width, height = WINDOW_SIZE
        if self.prefs["show_lines"]:
            height += LINES_BOX_HEIGHT + 8     # room for the Lines box, so the board keeps its size
        self.set_default_size(width, height)
        self.connect("destroy", self.on_destroy)

        self.engine = UCIEngine(engine_path)   # plays the engine's moves
        self.oracle = UCIEngine(engine_path)   # rules questions for the notation converter
        self.converter = NotationConverter(self.oracle)
        # always-on analysis (evaluation, suggestion, lines) on a third engine process
        self.analyzer = Analyzer(engine_path, self.converter,
                                 lambda gen, results: GLib.idle_add(self.on_analysis_lines, gen, results))

        self.start_fen = None                  # None = normal start position, else an imported engine FEN
        self.start_stm = "w"
        self.tree = GameTree(None)             # every move played, with its variations
        self.current = self.tree.root          # the position on the board
        self.move_spans = []                   # (start offset, end offset, node id) in the move list text
        self.side_delta = 0                    # how much the window grew when the move list was shown
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
        self.best_move = None                  # the engine's best move here (the Suggestion arrow)
        self.analysis_lines = []               # latest results of the always-on analysis
        self.analysis_fresh = True             # the next analysis starts with a cleared engine memory
        self.final_outcome = None              # set while the game on the board is over
        self.eval_info = None
        self.bar_pos = self.bar_target = 0.5   # eval bar: where it is drawn / where it is heading
        self.bar_timer = None
        self.lines_shown = False
        self.line_cache = None                 # what the Lines box shows now: (number of lines, texts)
        self.lines_delta = 0                   # window height added when the Lines box was shown
        self.side_shown = False
        self.piece_sets = find_piece_sets()    # {name: {(color, word): file}}
        self.piece_set_names = [TOKENS] + list(self.piece_sets)
        self.piece_images = None               # None = built-in tokens
        self.piece_set_name = TOKENS

        vbox = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        vbox.set_margin_top(8)
        vbox.set_margin_bottom(8)
        vbox.set_margin_start(8)
        vbox.set_margin_end(8)
        self.add(vbox)
        self.main_box = vbox

        # Row 1: game and mode
        row1 = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        vbox.pack_start(row1, False, False, 0)
        for label, handler in (
            ("New Game", lambda _: self.new_game()),
            ("Play as White", lambda _: self.set_mode("white")),
            ("Play as Black", lambda _: self.set_mode("black")),
            ("Analysis Mode", lambda _: self.set_mode("analysis")),
        ):
            btn = Gtk.Button(label=label)
            btn.connect("clicked", handler)
            row1.pack_start(btn, False, False, 0)

        # Strength sits at the right edge of row 1, exactly above Think Time on row 2.
        self.strength_spin = Gtk.SpinButton.new_with_range(1, 8, 1)
        self.strength_spin.set_value(DEFAULT_STRENGTH)
        self.strength_spin.set_tooltip_text(
            "How strong the engine is when it plays a move: 1 = weakest, 8 = full strength.\n"
            "The analysis (Eval, Lines, Suggestion) always uses full strength.")
        self.pack_spin_right(row1, "Strength (1-8):", self.strength_spin)

        # Row 2: position and view
        row2 = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        vbox.pack_start(row2, False, False, 0)

        btn_import = Gtk.Button(label="Import Position")
        btn_import.connect("clicked", self.on_import)
        row2.pack_start(btn_import, False, False, 0)

        btn_flip = Gtk.Button(label="Flip Board")
        btn_flip.connect("clicked", self.on_flip)
        row2.pack_start(btn_flip, False, False, 0)

        # The three view toggles.  They only show or hide things: the engine analyses all the time.
        self.eval_chk = self.add_toggle(row2, "Eval", "Show the evaluation bar (White's point of view)")
        self.lines_chk = self.add_toggle(row2, "Lines", "Show the engine's best lines")
        self.best_chk = self.add_toggle(row2, "Suggestion", "Draw the engine's best move on the board")

        self.time_spin = Gtk.SpinButton.new_with_range(0.5, 30.0, 0.5)
        self.time_spin.set_value(2.0)
        self.time_spin.set_tooltip_text("Thinking time per engine move at Strength 8 (levels 1-7 use short fixed times).")
        self.pack_spin_right(row2, "Think Time (sec):", self.time_spin)

        # Status & Eval labels
        self.status_label = Gtk.Label(label="Ready")
        self.status_label.set_xalign(0)
        vbox.pack_start(self.status_label, False, False, 2)

        eval_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        vbox.pack_start(eval_row, False, False, 2)
        self.eval_row = eval_row

        # "+0.3 [=====bar=====] Depth: 18" -- shown while the Eval toggle is ticked
        self.eval_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        self.eval_score = Gtk.Label(label="--")
        self.eval_score.set_width_chars(5)
        self.eval_score.set_xalign(1)
        self.eval_score.set_tooltip_text("From White's point of view: + = White ahead, - = Black ahead, # = mate")
        self.eval_box.pack_start(self.eval_score, False, False, 0)
        self.eval_bar = Gtk.DrawingArea()
        self.eval_bar.set_size_request(100, 14)
        self.eval_bar.set_valign(Gtk.Align.CENTER)
        self.eval_bar.connect("draw", self.on_draw_eval)
        self.eval_box.pack_start(self.eval_bar, True, True, 0)
        self.eval_depth = Gtk.Label(label="Depth: --")
        self.eval_depth.set_width_chars(10)
        self.eval_depth.set_xalign(0)
        self.eval_box.pack_start(self.eval_depth, False, False, 0)
        for widget in (self.eval_score, self.eval_bar, self.eval_depth):
            widget.show()                      # shown individually: show_all() skips the hidden box
        self.eval_box.set_no_show_all(True)
        eval_row.pack_start(self.eval_box, True, True, 0)

        # Right end of the line, right to left: Move List, Redo Move, Undo Move, then Visual Settings
        self.move_chk = Gtk.CheckButton(label="Move List")
        self.move_chk.set_tooltip_text("Show the moves next to the board")
        self.move_chk.connect("toggled", self.on_move_list_toggled)
        eval_row.pack_end(self.move_chk, False, False, 0)

        self.btn_redo = Gtk.Button(label="Redo Move")
        self.btn_redo.connect("clicked", self.on_redo)
        self.make_compact(self.btn_redo)
        eval_row.pack_end(self.btn_redo, False, False, 0)

        self.btn_undo = Gtk.Button(label="Undo Move")
        self.btn_undo.connect("clicked", self.on_undo)
        self.make_compact(self.btn_undo)
        eval_row.pack_end(self.btn_undo, False, False, 0)

        # Visual Settings: pieces, board colours, where the engine lines go, Light / Dark mode
        self.btn_visual = Gtk.Button(label="Visual Settings")
        self.btn_visual.set_tooltip_text("Pieces, board colors, engine lines position, Light / Dark mode")
        self.btn_visual.connect("clicked", self.on_visual_settings)
        self.make_compact(self.btn_visual)
        eval_row.pack_end(self.btn_visual, False, False, 0)
        wanted = self.prefs["piece_set"] or DEFAULT_PIECE_SET
        self.load_piece_set(wanted if wanted in self.piece_set_names else TOKENS)  # the board is not built yet

        # Engine lines: a box of fixed height (about three lines, more lines scroll) with the number of
        # lines and the number of threads beside it.  Visible while the Lines toggle is ticked.
        self.lines_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        scroll = Gtk.ScrolledWindow()
        scroll.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        scroll.set_shadow_type(Gtk.ShadowType.IN)
        scroll.set_size_request(-1, LINES_BOX_HEIGHT)
        scroll.set_min_content_height(LINES_BOX_HEIGHT)
        scroll.get_style_context().add_class("dragon-surface")      # same white as the move list
        inner = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
        inner.get_style_context().add_class("dragon-surface")
        inner.set_margin_start(6)
        inner.set_margin_top(3)
        inner.set_margin_bottom(3)
        self.line_labels = []
        for _ in range(MAX_LINES):
            lbl = Gtk.Label(label="")
            lbl.set_xalign(0)
            lbl.set_ellipsize(Pango.EllipsizeMode.END)
            inner.pack_start(lbl, False, False, 0)
            self.line_labels.append(lbl)
        scroll.add(inner)
        self.lines_row.pack_start(scroll, True, True, 0)

        controls = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
        controls.set_valign(Gtk.Align.CENTER)
        self.lines_spin = Gtk.SpinButton.new_with_range(1, MAX_LINES, 1)
        self.lines_spin.set_value(self.prefs["lines"])
        self.lines_spin.set_tooltip_text(
            f"How many lines the engine works out (1-{MAX_LINES}). The evaluation is the top line.\n"
            "More lines slow the search down a little.")
        self.pack_spin_row(controls, "Lines:", self.lines_spin)
        self.threads_spin = Gtk.SpinButton.new_with_range(1, max_threads(), 1)
        self.threads_spin.set_value(self.prefs["threads"])
        self.threads_spin.set_tooltip_text(
            f"CPU threads the analysis may use (1-{max_threads()}, the number of processors in this computer).\n"
            "More threads reach deeper in the same time.")
        self.pack_spin_row(controls, "Threads:", self.threads_spin)
        controls.show()
        self.lines_row.pack_start(controls, False, False, 0)
        for widget in (scroll, inner, *self.line_labels):
            widget.show()
        self.lines_row.set_no_show_all(True)
        vbox.pack_start(self.lines_row, False, False, 2)

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
        body = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        vbox.pack_start(body, True, True, 0)
        body.pack_start(self.area, True, True, 0)
        self.build_move_panel(body)
        self.place_lines_row()                   # Top or Bottom, as chosen in Visual Settings

        # connect the view toggles and the spin boxes, then apply the saved settings
        self.eval_chk.connect("toggled", self.on_eval_toggled)
        self.lines_chk.connect("toggled", self.on_lines_toggled)
        self.best_chk.connect("toggled", self.on_suggestion_toggled)
        self.lines_spin.connect("value-changed", self.on_analysis_setting_changed)
        self.threads_spin.connect("value-changed", self.on_analysis_setting_changed)
        self.eval_chk.set_active(self.prefs["show_eval"])
        self.lines_chk.set_active(self.prefs["show_lines"])
        self.best_chk.set_active(self.prefs["show_suggestion"])
        self.move_chk.set_active(self.prefs["show_move_list"])

        self.set_mode("white")
        self.new_game()
        self.loading_prefs = False

    # ----- move list panel -------------------------------------------------------
    def build_move_panel(self, body):
        """The scrollable move list with Import / Export PGN below it (hidden until 'Move List' is ticked)."""
        self.side = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        self.side.set_size_request(SIDE_WIDTH, -1)

        scroll = Gtk.ScrolledWindow()
        scroll.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        scroll.set_shadow_type(Gtk.ShadowType.IN)
        self.move_view = Gtk.TextView()
        self.move_view.set_editable(False)
        self.move_view.set_cursor_visible(False)
        self.move_view.set_monospace(True)
        self.move_view.set_wrap_mode(Gtk.WrapMode.WORD_CHAR)
        self.move_view.set_left_margin(6)
        self.move_view.set_right_margin(6)
        self.move_view.set_top_margin(4)
        self.move_view.set_bottom_margin(4)
        self.move_view.connect("button-release-event", self.on_move_list_click)
        self.move_view.get_style_context().add_class("dragon-surface")
        scroll.add(self.move_view)
        self.side.pack_start(scroll, True, True, 0)

        buf = self.move_view.get_buffer()
        self.theme_tags = {                                # the colours of these follow Light / Dark mode
            "num": buf.create_tag("num"),                  # move numbers
            "paren": buf.create_tag("paren"),              # the brackets around variations
            "current": buf.create_tag("current"),          # the move on the board
        }
        self.colour_move_tags()
        for level in range(1, MAX_INDENT + 1):             # one indent per variation level
            buf.create_tag(f"indent{level}", left_margin=6 + 14 * level)
        buf.create_mark("curmove", buf.get_start_iter(), True)

        buttons = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        btn_in = Gtk.Button(label="Import PGN")
        btn_in.connect("clicked", self.on_import_pgn)
        buttons.pack_start(btn_in, True, True, 0)
        btn_out = Gtk.Button(label="Export PGN")
        btn_out.connect("clicked", self.on_export_pgn)
        buttons.pack_start(btn_out, True, True, 0)
        self.side.pack_start(buttons, False, False, 0)

        # show_all() skips a no-show-all widget, so its children are shown one by one
        for widget in (scroll, self.move_view, buttons, btn_in, btn_out):
            widget.show()
        self.side.set_no_show_all(True)
        body.pack_start(self.side, False, False, 0)

    def on_move_list_toggled(self, chk):
        show = chk.get_active()
        if show == self.side_shown:
            return
        self.side_shown = show
        if show:
            self.side.show()
            self.side_delta = 0
            if not self.loading_prefs:
                # grow the window by the panel width, minus the blank space beside the board
                alloc = self.area.get_allocation()
                gap = max(0, alloc.width - min(alloc.width, alloc.height))
                self.side_delta = max(0, SIDE_WIDTH + 8 - gap)
                self.grow_window(dw=self.side_delta)
            self.refresh_move_list()
        else:
            self.side.hide()
            self.grow_window(dw=-self.side_delta)
            self.side_delta = 0
        self.save_prefs()

    def refresh_move_list(self):
        """Rebuild the move list text from the game tree and highlight the current move."""
        if not self.move_chk.get_active():
            return
        buf = self.move_view.get_buffer()
        buf.set_text("")
        self.move_spans = []
        pos, current_span = 0, None
        for seg in layout_move_list(self.tree):
            names = [seg.style] if seg.style in ("num", "paren") else []
            if seg.level:
                names.append(f"indent{min(seg.level, MAX_INDENT)}")
            buf.insert_with_tags_by_name(buf.get_end_iter(), seg.text, *names)
            end = pos + len(seg.text)
            if seg.node is not None:
                self.move_spans.append((pos, end, seg.node.id))
                if seg.node is self.current:
                    current_span = (pos, end)
            pos = end
        if current_span:
            start = buf.get_iter_at_offset(current_span[0])
            buf.apply_tag_by_name("current", start, buf.get_iter_at_offset(current_span[1]))
            buf.move_mark_by_name("curmove", start)
            self.move_view.scroll_to_mark(buf.get_mark("curmove"), 0.1, False, 0.0, 0.0)
        else:
            self.move_view.scroll_to_mark(buf.get_mark("curmove"), 0.0, True, 0.0, 0.0)

    def node_at_offset(self, offset):
        """The game tree node whose move is written at this character offset of the list, or None."""
        i = bisect.bisect_right([span[0] for span in self.move_spans], offset) - 1
        if i >= 0 and self.move_spans[i][0] <= offset < self.move_spans[i][1]:
            return self.tree.nodes.get(self.move_spans[i][2])
        return None

    def on_move_list_click(self, view, event):
        if event.button != 1 or view.get_buffer().get_has_selection():
            return False                        # not a plain left click (e.g. the end of a text selection)
        x, y = view.window_to_buffer_coords(Gtk.TextWindowType.WIDGET, int(event.x), int(event.y))
        found = view.get_iter_at_location(x, y)     # newer GTK returns (over_text, iter)
        over_text, it = found if isinstance(found, tuple) else (True, found)
        node = self.node_at_offset(it.get_offset()) if over_text else None
        if node is not None:
            self.go_to(node)
        return False

    def load_piece_set(self, name):
        """Select the named picture set (TOKENS = the built-in drawn pieces)."""
        files = self.piece_sets.get(name)
        self.piece_set_name = name
        self.piece_images = PieceImages(files) if files else None
        if files and len(files) < len(ALL_PIECE_KEYS):
            print(f"[PIECES] '{name}' is incomplete, missing pieces are drawn as tokens")

    def use_piece_set(self, name):
        self.load_piece_set(name)
        self.area.queue_draw()
        self.refresh_visual_window()
        self.save_prefs()

    # ----- visual settings: board colours, engine lines position, Light / Dark mode --------------
    def on_visual_settings(self, _btn):
        if self.visual_win is not None:
            self.visual_win.present()
            return
        self.visual_win = VisualSettingsWindow(self)
        self.visual_win.show_all()
        self.visual_win.after_show()

    def refresh_visual_window(self):
        if self.visual_win is not None:
            self.visual_win.refresh_previews()

    def current_scheme_hexes(self):
        return scheme_hexes(self.board_scheme, self.custom_light, self.custom_dark)

    def update_board_colours(self):
        self.board_colours = board_colours(self.board_scheme, self.custom_light, self.custom_dark)
        self.area.queue_draw()
        self.refresh_visual_window()

    def set_board_scheme(self, scheme):
        if scheme == self.board_scheme or scheme not in dict(SCHEME_CHOICES):
            return
        if scheme == CUSTOM and not (self.custom_light and self.custom_dark):
            # the first time: Custom starts from the colours that are on the board now
            self.custom_light, self.custom_dark = self.current_scheme_hexes()
        self.board_scheme = scheme
        self.update_board_colours()
        self.save_prefs()

    def set_custom_colour(self, which, hex_colour, commit=True):
        """Set the Custom board's 'light' or 'dark' square colour.  commit=False only shows it (while the
        colour picker is still open); the colour is saved when it is set again with commit=True."""
        rgb = parse_hex_colour(hex_colour)
        if rgb is None or which not in ("light", "dark"):
            return
        if which == "light":
            self.custom_light = to_hex(rgb)
        else:
            self.custom_dark = to_hex(rgb)
        self.update_board_colours()
        if commit:
            self.save_prefs()

    def place_lines_row(self):
        """Top: just above the Eval line (so below the status line).  Bottom: the last thing in the window."""
        box = self.main_box
        if self.lines_position == "top":
            children = box.get_children()
            target = children.index(self.eval_row)
            if children.index(self.lines_row) < target:
                target -= 1                      # it is leaving a place before the Eval line
            box.reorder_child(self.lines_row, target)
        else:
            box.reorder_child(self.lines_row, -1)

    def set_lines_position(self, position):
        if position not in LINES_POSITIONS or position == self.lines_position:
            return
        self.lines_position = position
        self.place_lines_row()
        self.refresh_visual_window()
        self.save_prefs()

    def colour_move_tags(self):
        """Colour the move list's tags for the current Light / Dark mode."""
        theme = self.theme
        self.theme_tags["num"].set_property("foreground", theme["muted"])
        self.theme_tags["paren"].set_property("foreground", theme["muted"])
        self.theme_tags["current"].set_property("background", theme["current_bg"])
        self.theme_tags["current"].set_property("foreground", theme["current_fg"])

    def set_theme(self, name):
        """Switch every window between Light and Dark mode."""
        if name not in THEMES or name == self.theme_name:
            return
        self.theme_name = name
        self.theme = apply_gtk_theme(name)
        self.colour_move_tags()
        self.eval_bar.queue_draw()
        self.area.queue_draw()
        for window in (self, self.visual_win):
            if window is not None and os.name == "nt":
                set_titlebar_dark(window)
        self.refresh_visual_window()
        self.save_prefs()

    # ----- evaluation bar -------------------------------------------------------------
    def show_eval(self, info):
        """Show the evaluation of a result (None = nothing known yet): score, bar and depth."""
        self.eval_info = info
        self.eval_score.set_text(format_eval_short(info))
        depth = info.get("depth") if info else None
        self.eval_depth.set_text(f"Depth: {depth}" if depth is not None else "Depth: --")
        self.set_bar_target(eval_fraction(info))

    def clear_eval(self):
        self.show_eval(None)

    def show_final_eval(self, winner):
        """The game on the board is over: show the result instead of an evaluation."""
        self.eval_info = None
        self.eval_score.set_text({"w": "1-0", "b": "0-1", None: "\u00bd-\u00bd"}[winner])
        self.eval_depth.set_text("Game over")
        self.set_bar_target({"w": 1.0, "b": 0.0, None: 0.5}[winner])

    def set_bar_target(self, share):
        """Slide the bar towards `share` (White's part, 0..1)."""
        self.bar_target = share
        if not self.eval_chk.get_active():
            self.bar_pos = share                 # hidden: nothing to animate
        elif self.bar_timer is None and abs(self.bar_pos - share) > 0.003:
            self.bar_timer = GLib.timeout_add(16, self.step_bar)
        self.eval_bar.queue_draw()

    def step_bar(self):
        """One animation frame (about 60 per second): the bar covers a fifth of the remaining way."""
        gap = self.bar_target - self.bar_pos
        if abs(gap) < 0.003:
            self.bar_pos = self.bar_target
            self.bar_timer = None
            self.eval_bar.queue_draw()
            return False
        self.bar_pos += gap * 0.2
        self.eval_bar.queue_draw()
        return True

    def on_draw_eval(self, widget, cr):
        alloc = widget.get_allocation()
        draw_eval_bar(cr, alloc.width, alloc.height, self.bar_pos, self.theme)
        return False

    # ----- view toggles, spin boxes and saved settings -----------------------------------
    @staticmethod
    def add_toggle(row, text, tooltip):
        """"Text [ ]" -- the label first, then its check box.  Returns the check box."""
        box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=2)
        box.pack_start(Gtk.Label(label=text), False, False, 0)
        chk = Gtk.CheckButton()
        chk.set_tooltip_text(tooltip)
        box.pack_start(chk, False, False, 0)
        row.pack_start(box, False, False, 0)
        return chk

    @staticmethod
    def pack_spin_row(box, text, spin):
        """"Label [spin]" as one line of a vertical box; the spin boxes line up."""
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        label = Gtk.Label(label=text)
        label.set_width_chars(8)
        label.set_xalign(1)
        spin.set_width_chars(3)
        row.pack_start(label, False, False, 0)
        row.pack_start(spin, False, False, 0)
        row.show_all()
        box.pack_start(row, False, False, 0)

    def grow_window(self, dw=0, dh=0):
        """Make the window dw / dh pixels bigger (smaller if negative); growing stops at the screen size."""
        width, height = self.get_size()
        new_w, new_h = width + dw, height + dh
        try:
            screen = Gdk.Screen.get_default()
            if screen is not None:
                if dw > 0:
                    new_w = max(width, min(new_w, screen.get_width() - 40))
                if dh > 0:
                    new_h = max(height, min(new_h, screen.get_height() - 80))
        except Exception:
            pass
        self.resize(max(1, new_w), max(1, new_h))

    def on_eval_toggled(self, chk):
        if chk.get_active():
            self.eval_box.show()
            self.bar_pos = self.bar_target       # no sliding from wherever it was while hidden
            self.eval_bar.queue_draw()
        else:
            self.eval_box.hide()
        self.save_prefs()

    def on_lines_toggled(self, chk):
        show = chk.get_active()
        if show == self.lines_shown:
            return
        self.lines_shown = show
        self.analyzer.want_text = show           # the notation is only worked out while it is visible
        if show:
            self.lines_row.show()
            self.lines_delta = LINES_BOX_HEIGHT + 8
            if not self.loading_prefs:           # keep the board the same size
                self.grow_window(dh=self.lines_delta)
            self.analyzer.nudge()
        else:
            self.lines_row.hide()
            self.grow_window(dh=-self.lines_delta)
            self.lines_delta = 0
        self.refresh_lines_panel()
        self.save_prefs()

    def on_suggestion_toggled(self, chk):
        self.area.queue_draw()
        self.save_prefs()

    def on_analysis_setting_changed(self, _spin):
        """Lines or Threads changed: the only settings that make the analysis start again."""
        self.save_prefs()
        if not self.loading_prefs:
            self.update_analysis()

    def current_prefs(self):
        return {
            "piece_set": self.piece_set_name,
            "show_eval": self.eval_chk.get_active(),
            "show_lines": self.lines_chk.get_active(),
            "show_suggestion": self.best_chk.get_active(),
            "show_move_list": self.move_chk.get_active(),
            "lines": int(self.lines_spin.get_value()),
            "threads": int(self.threads_spin.get_value()),
            "board_scheme": self.board_scheme,
            "custom_light": self.custom_light,
            "custom_dark": self.custom_dark,
            "lines_position": self.lines_position,
            "theme": self.theme_name,
        }

    def save_prefs(self):
        if not self.loading_prefs:
            save_settings(self.current_prefs(), self.prefs_path)

    @staticmethod
    def pack_spin_right(row, text, spin):
        """Put "label [spin]" at the right edge of a row. Both rows use the same label and spin
        widths, so the two spin boxes line up exactly above each other."""
        spin.set_width_chars(5)
        row.pack_end(spin, False, False, 0)   # pack_end: the first widget packed is the right-most
        label = Gtk.Label(label=text)
        label.set_width_chars(17)
        label.set_xalign(1)
        row.pack_end(label, False, False, 4)

    @staticmethod
    def make_compact(button):
        """Shrink a button's padding so it fits on a line of text."""
        try:
            css = Gtk.CssProvider()
            css.load_from_data(b"button.compact { padding: 0px 8px; min-height: 0px; min-width: 0px; }")
            Gtk.StyleContext.add_provider_for_screen(
                Gdk.Screen.get_default(), css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
            button.get_style_context().add_class("compact")
        except Exception:
            pass  # purely cosmetic: keep the normal button if styling is unavailable

    def on_destroy(self, *_):
        try:
            self.cancel_engine_move()
            self.save_prefs()
            self.analyzer.close()
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
        self.start_fen, self.start_stm = None, "w"
        self.tree = GameTree(None)
        self.current = self.tree.root
        self.selected_sq = None
        self.last_move = None
        self.notes.clear()
        self.engine.new_game()
        self.analysis_fresh = True
        self.clear_eval()
        self.sync_board()
        self.maybe_engine_move()

    def on_undo(self, _):
        was_thinking = self.thinking
        self.cancel_engine_move()
        keep = undo_length(self.start_stm, self.current.ply, self.human_sides)
        if keep is None and not was_thinking:
            return
        if keep is not None:
            self.current = self.tree.ancestor(self.current, keep)   # the moves stay in the tree
            self.selected_sq = None
            self.last_move = self.current.move
            self.notes.clear()
        self.sync_board()
        self.maybe_engine_move()

    def on_redo(self, _):
        """Step forward along the line you came from; against the engine: your move and its reply."""
        was_thinking = self.thinking
        self.cancel_engine_move()
        node, steps = self.current, 0
        while True:
            nxt = self.tree.redo_child(node)
            if nxt is None:
                break
            node, steps = nxt, steps + 1
            if self.tree.stm_after(node) in self.human_sides:
                break
        if steps == 0 and not was_thinking:
            return
        if steps:
            self.current = node
            self.tree.visit(node)
            self.selected_sq = None
            self.last_move = node.move
            self.notes.clear()
        self.sync_board()
        self.maybe_engine_move()

    def go_to(self, node):
        """Jump to any move of the game (move list click). The engine only carries on by itself when
        this is the end of a line, so browsing an old game does not make it start thinking."""
        if node is self.current:
            return
        self.cancel_engine_move()
        self.current = node
        self.tree.visit(node)
        self.selected_sq = None
        self.last_move = node.move
        self.notes.clear()
        self.sync_board()
        if not node.children:
            self.maybe_engine_move()

    def push_move(self, uci):
        """Play `uci` from the current position: follow the existing branch or add a new one."""
        parent = self.current
        child = parent.child_for(uci)
        if child is None:
            try:
                san, fen = self.converter.san_move(self.start_fen, self.tree.moves(parent), uci)
            except Exception:
                san, fen = uci, None          # notation is cosmetic: never let it block a move
            child = self.tree.add(parent, uci, san, fen)
        self.current = child
        self.tree.visit(child)
        self.last_move = uci

    def on_flip(self, _):
        self.flipped = not self.flipped
        self.area.queue_draw()

    @property
    def moves(self):
        """UCI moves from the start position to the position on the board."""
        return self.tree.moves(self.current)

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
        self.fen, self.legal_moves, self.in_check = self.engine.get_state(self.moves, self.start_fen)
        turn = "White" if self.turn_color() == "w" else "Black"
        mode = MODES[self.mode][1]
        self.btn_undo.set_sensitive(undo_length(self.start_stm, self.current.ply, self.human_sides) is not None)
        self.btn_redo.set_sensitive(self.tree.redo_child(self.current) is not None)
        self.final_outcome = None
        if not self.legal_moves:
            prev_fen = None
            if self.moves:  # position before the last move, to tell a baremate from a stalemate
                prev_fen = self.engine.get_state(self.moves[:-1], self.start_fen, quiet=True)[0]
            self.final_outcome = game_outcome(self.fen, self.in_check, prev_fen)
            self.status_label.set_text(game_over_text(self.fen, self.in_check, prev_fen))
        else:
            chk = " (IN CHECK!)" if self.in_check else ""
            self.status_label.set_text(
                f"Mode: {mode} | Move: {turn}{chk} | Legal moves: {len(self.legal_moves)} | "
                f"FEN: {engine_fen_to_designer(self.fen)}"
            )
        self.update_analysis()
        self.area.queue_draw()
        self.refresh_move_list()

    # ----- importing a position ------------------------------------------------
    def check_start_position(self, engine_fen):
        """Raise ValueError unless the engine can load this position and the side NOT to move is not
        already in check (the engine happily loads illegal positions, so this has to be checked here)."""
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

    def load_position(self, text, notation=AUTO):
        """Set the board from pasted FEN text.  Returns the notation that was detected.
        Raises ValueError (with a readable message) and changes nothing if it is not usable."""
        engine_fen, used = parse_import_fen(text, notation)
        self.check_start_position(engine_fen)

        self.cancel_engine_move()
        self.start_fen, self.start_stm = engine_fen, engine_fen.split()[1]
        self.tree = GameTree(engine_fen)
        self.current = self.tree.root
        self.selected_sq = None
        self.last_move = None
        self.notes.clear()
        self.engine.new_game()
        self.analysis_fresh = True
        self.clear_eval()
        self.sync_board()
        self.maybe_engine_move()
        return used

    def on_import(self, _):
        dialog = Gtk.Dialog(title="Import Position", transient_for=self, flags=0)
        watch_titlebar(dialog)
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

    # ----- PGN import / export ---------------------------------------------------------
    def pgn_text(self):
        """The whole game tree as PGN text.  The result is only filled in when the main line has
        ended the game (checkmate, stalemate, baremate or the lone-Queen draw)."""
        moves = self.tree.moves(self.tree.main_end())
        result = "*"
        fen, legal, in_check = self.oracle.get_state(moves, self.start_fen, quiet=True)
        if fen and not legal:
            prev_fen = self.oracle.get_state(moves[:-1], self.start_fen, quiet=True)[0] if moves else None
            result = pgn_result(fen, in_check, prev_fen)
        return tree_to_pgn(self.tree, result)

    def import_pgn_text(self, text):
        """Replace the game by the first game in this PGN text, variations included.  Raises
        ValueError (readable message) and changes nothing if the text cannot be used."""
        tree = pgn_to_tree(text, self.converter)
        if tree.start_fen:
            self.check_start_position(tree.start_fen)
        self.cancel_engine_move()
        self.start_fen, self.start_stm = tree.start_fen, tree.start_stm
        self.tree = tree
        self.current = tree.main_end()               # show the end of the main line
        tree.visit(self.current)
        self.selected_sq = None
        self.last_move = self.current.move
        self.notes.clear()
        self.engine.new_game()
        self.analysis_fresh = True
        self.clear_eval()
        self.sync_board()
        self.maybe_engine_move()

    @staticmethod
    def pgn_file_dialog(parent, title, action):
        dialog = Gtk.FileChooserDialog(title=title, transient_for=parent, action=action)
        watch_titlebar(dialog)
        dialog.add_buttons("Cancel", Gtk.ResponseType.CANCEL,
                           "Save" if action == Gtk.FileChooserAction.SAVE else "Open", Gtk.ResponseType.OK)
        pgn = Gtk.FileFilter()
        pgn.set_name("PGN files (*.pgn)")
        pgn.add_pattern("*.pgn")
        pgn.add_pattern("*.PGN")
        dialog.add_filter(pgn)
        everything = Gtk.FileFilter()
        everything.set_name("All files")
        everything.add_pattern("*")
        dialog.add_filter(everything)
        return dialog

    def on_export_pgn(self, _):
        try:
            text = self.pgn_text()
        except Exception as e:
            show_error(f"Could not prepare the PGN:\n{e}", self)
            return
        dialog = self.pgn_file_dialog(self, "Export PGN", Gtk.FileChooserAction.SAVE)
        dialog.set_do_overwrite_confirmation(True)
        dialog.set_current_name("dragonanga.pgn")
        path = dialog.get_filename() if dialog.run() == Gtk.ResponseType.OK else None
        dialog.destroy()
        if not path:
            return
        if not os.path.splitext(path)[1]:
            path += ".pgn"
        try:
            with open(path, "w", encoding="utf-8", newline="\n") as f:
                f.write(text)
        except OSError as e:
            show_error(f"Could not save the file:\n{path}\n\n{e}", self)

    def on_import_pgn(self, _):
        dialog = Gtk.Dialog(title="Import PGN", transient_for=self, flags=0)
        watch_titlebar(dialog)
        dialog.add_button("Cancel", Gtk.ResponseType.CANCEL)
        dialog.add_button("Import", Gtk.ResponseType.OK)
        dialog.set_default_size(560, 400)
        box = dialog.get_content_area()
        box.set_spacing(6)

        intro = Gtk.Label(label="Paste a PGN below, or open a .pgn file. Moves use the designer letters "
                                "(Sc3, Gb4, Qxe7+ ...); variations in brackets are kept.")
        intro.set_xalign(0)
        intro.set_line_wrap(True)
        intro.set_max_width_chars(70)
        box.pack_start(intro, False, False, 0)

        scroll = Gtk.ScrolledWindow()
        scroll.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        scroll.set_shadow_type(Gtk.ShadowType.IN)
        view = Gtk.TextView()
        view.set_monospace(True)
        view.set_wrap_mode(Gtk.WrapMode.WORD_CHAR)
        view.get_style_context().add_class("dragon-surface")
        scroll.add(view)
        box.pack_start(scroll, True, True, 0)
        buf = view.get_buffer()

        err = Gtk.Label(label="")
        err.set_xalign(0)
        err.set_line_wrap(True)
        err.set_max_width_chars(70)

        def open_file(_btn):
            chooser = self.pgn_file_dialog(dialog, "Open PGN file", Gtk.FileChooserAction.OPEN)
            path = chooser.get_filename() if chooser.run() == Gtk.ResponseType.OK else None
            chooser.destroy()
            if not path:
                return
            try:
                with open(path, encoding="utf-8-sig", errors="replace") as f:
                    buf.set_text(f.read())
                err.set_text("")
            except OSError as e:
                err.set_text(f"Could not read the file: {e}")

        btn_open = Gtk.Button(label="Open file...")
        btn_open.connect("clicked", open_file)
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        row.pack_start(btn_open, False, False, 0)
        box.pack_start(row, False, False, 0)
        box.pack_start(err, False, False, 0)

        dialog.show_all()
        while dialog.run() == Gtk.ResponseType.OK:
            text = buf.get_text(buf.get_start_iter(), buf.get_end_iter(), True)
            try:
                self.import_pgn_text(text)
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

    def trigger_engine_move(self):
        self.thinking = True
        self.engine_gen += 1
        gen = self.engine_gen
        cancel = threading.Event()
        self.engine_cancel = cancel
        self.status_label.set_text("Fairy-Stockfish is thinking...")
        skill, depth, movetime_ms = strength_settings(
            self.strength_spin.get_value(), int(self.time_spin.get_value() * 1000))
        moves, start_fen = list(self.moves), self.start_fen

        def worker():
            try:
                best = self.engine.search(moves, movetime_ms, lambda line: None, cancel=cancel,
                                          start_fen=start_fen, skill=skill, depth=depth)
            except (OSError, ValueError):
                return                    # the engine process is gone (the window is closing)
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

    def finish_engine_move(self, gen, bestmove):
        if gen != self.engine_gen:
            return False
        self.thinking = False
        self.engine_cancel = None
        if bestmove and bestmove != "(none)":
            self.push_move(bestmove)
        self.sync_board()
        self.maybe_engine_move()
        return False

    # ----- always-on analysis (evaluation, Suggestion arrow, Lines) --------------------------
    def update_analysis(self):
        """Aim the analysis at the position on the board.  If it is already analysing exactly this
        position (a view toggle, a change of side or mode...), nothing is restarted."""
        if not self.legal_moves:                      # game over
            self.analyzer.stop()
            self.best_move, self.analysis_lines = None, []
            outcome = self.final_outcome
            self.show_final_eval(outcome[1] if outcome else None)
        else:
            restarted = self.analyzer.analyse(
                self.start_fen, list(self.moves), self.turn_color(), self.fullmove_number(),
                int(self.lines_spin.get_value()), int(self.threads_spin.get_value()), fresh=self.analysis_fresh)
            self.analysis_fresh = False
            if restarted:                             # the old arrow and lines belong to the old position
                self.best_move, self.analysis_lines = None, []
        self.refresh_lines_panel()

    def on_analysis_lines(self, gen, results):
        if gen != self.analyzer.gen or not results:
            return False                              # a result of a position we have left
        self.analysis_lines = results
        top = results[0]
        previous = self.best_move
        self.best_move = top["pv"][0] if top["pv"] else None
        self.show_eval(top)
        self.refresh_lines_panel()
        if self.best_chk.get_active() and self.best_move != previous:
            self.area.queue_draw()
        return False

    def refresh_lines_panel(self):
        """Fill the Lines box (the labels are only rewritten, the box never changes size)."""
        shown = int(self.lines_spin.get_value())
        rows = [""] * MAX_LINES
        if self.lines_chk.get_active():
            if not self.legal_moves:
                pass
            elif not self.is_human_turn():
                rows[0] = "(lines are shown on your turn)"
            elif self.analysis_lines:
                for i, info in enumerate(self.analysis_lines[:shown]):
                    rows[i] = format_line_row(info)
            else:
                rows[0] = "Analysing\u2026"
        if (shown, rows) == self.line_cache:
            return                                    # nothing to change (this runs several times a second)
        self.line_cache = (shown, rows)
        for i, lbl in enumerate(self.line_labels):
            if i < shown:
                lbl.show()
            else:
                lbl.hide()
            lbl.set_markup(f"<tt>{html.escape(rows[i])}</tt>")
            lbl.set_tooltip_text(rows[i] or None)

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
        watch_titlebar(dialog)
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
        self.push_move(uci_move)
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
            self.last_move, self.notes,
            self.best_move if self.best_chk.get_active() and self.legal_moves and self.is_human_turn() else None,
            self.piece_images,
            self.board_colours,
        )


# ---------------------------------------------------------------------------
# Visual Settings window, its colour picker and the Light / Dark switch
# ---------------------------------------------------------------------------
class ThemeSwitch:
    """The sliding Light / Dark switch: the moon (Dark Mode) on the left, the sun (Light Mode) on the
    right.  Click it, or use the space bar / arrow keys when it has the focus."""
    WIDTH, HEIGHT = 64, 30

    def __init__(self, light, on_toggle):
        self.light = light
        self.on_toggle = on_toggle               # called with True (Light) / False (Dark) after a click
        self.pos = self.target = 1.0 if light else 0.0
        self.timer = None
        self.gone = False
        self.widget = Gtk.DrawingArea()
        self.widget.set_size_request(self.WIDTH, self.HEIGHT)
        self.widget.set_can_focus(True)
        self.widget.add_events(Gdk.EventMask.BUTTON_PRESS_MASK | Gdk.EventMask.KEY_PRESS_MASK)
        self.widget.set_tooltip_text("Light Mode (sun) / Dark Mode (moon)")
        self.widget.connect("draw", self.on_draw)
        self.widget.connect("button-press-event", self.on_press)
        self.widget.connect("key-press-event", self.on_key)
        self.widget.connect("destroy", self.on_destroy)

    def on_destroy(self, *_):
        self.gone = True

    def on_draw(self, widget, cr):
        draw_theme_switch(cr, self.WIDTH, self.HEIGHT, self.pos)
        return False

    def set_light(self, light):
        """Slide the knob to Light or Dark without telling anyone."""
        self.light = light
        self.target = 1.0 if light else 0.0
        if self.timer is None and abs(self.pos - self.target) > 0.01:
            self.timer = GLib.timeout_add(16, self.step)
        self.widget.queue_draw()

    def step(self):
        gap = self.target - self.pos
        if self.gone or abs(gap) < 0.01:
            self.pos = self.target
            self.timer = None
            if not self.gone:
                self.widget.queue_draw()
            return False
        self.pos += gap * 0.25
        self.widget.queue_draw()
        return True

    def choose(self, light):
        if light != self.light:
            self.set_light(light)
            self.on_toggle(light)

    def on_press(self, widget, event):
        if event.button == 1:
            widget.grab_focus()
            self.choose(not self.light)
        return True

    def on_key(self, widget, event):
        key = event.keyval
        if key in (Gdk.KEY_space, Gdk.KEY_Return, Gdk.KEY_KP_Enter):
            self.choose(not self.light)
        elif key == Gdk.KEY_Left:
            self.choose(False)
        elif key == Gdk.KEY_Right:
            self.choose(True)
        else:
            return False
        return True


class ColourPickerDialog(Gtk.Dialog):
    """A colour picker that needs nothing but GTK (so it looks and works the same on Windows and Linux):
    click or drag in the square and on the rainbow bar, type the Red / Green / Blue numbers, or type
    a hex code.  `on_change(hex)` is called on every change, so the board can follow along."""
    SV_W, SV_H, HUE_H = 230, 170, 20

    def __init__(self, parent, title, start_hex, on_change=None):
        super().__init__(title=title, transient_for=parent, flags=0)
        watch_titlebar(self)
        self.on_change = on_change
        self.syncing = False                     # True while the boxes are being filled in by the program
        self.drag = None                         # "sv" or "hue" while the mouse button is down
        self.start_rgb = parse_hex_colour(start_hex) or (255, 255, 255)
        self.rgb = self.start_rgb
        self.h, self.s, self.v = rgb_to_hsv(self.rgb)

        self.add_button("Cancel", Gtk.ResponseType.CANCEL)
        self.add_button("OK", Gtk.ResponseType.OK)
        self.set_default_response(Gtk.ResponseType.OK)
        box = self.get_content_area()
        box.set_spacing(10)
        box.set_border_width(10)
        main = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=18)
        box.pack_start(main, True, True, 0)

        left = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=10)
        main.pack_start(left, False, False, 0)
        self.sv_area = self.make_area(self.SV_W, self.SV_H, self.on_draw_sv, "sv")
        self.hue_area = self.make_area(self.SV_W, self.HUE_H, self.on_draw_hue, "hue")
        left.pack_start(self.sv_area, False, False, 0)
        left.pack_start(self.hue_area, False, False, 0)

        right = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=12)
        main.pack_start(right, True, True, 0)

        compare = Gtk.Grid()
        compare.set_column_spacing(8)
        compare.set_row_spacing(4)
        self.new_area = Gtk.DrawingArea()
        self.new_area.set_size_request(96, 30)
        self.new_area.connect("draw", lambda w, cr: self.paint_swatch(w, cr, self.rgb))
        self.old_area = Gtk.DrawingArea()
        self.old_area.set_size_request(96, 30)
        self.old_area.connect("draw", lambda w, cr: self.paint_swatch(w, cr, self.start_rgb))
        for row, (text, area) in enumerate((("New", self.new_area), ("Current", self.old_area))):
            label = Gtk.Label(label=text)
            label.set_xalign(0)
            compare.attach(label, 0, row, 1, 1)
            compare.attach(area, 1, row, 1, 1)
        right.pack_start(compare, False, False, 0)

        fields = Gtk.Grid()
        fields.set_column_spacing(8)
        fields.set_row_spacing(6)
        self.spins = []
        for row, (letter, value) in enumerate(zip("RGB", self.rgb)):
            label = Gtk.Label(label=letter)
            label.set_xalign(1)
            spin = Gtk.SpinButton.new_with_range(0, 255, 1)
            spin.set_value(value)
            spin.set_width_chars(4)
            fields.attach(label, 0, row, 1, 1)
            fields.attach(spin, 1, row, 1, 1)
            self.spins.append(spin)
        hex_label = Gtk.Label(label="Hex")
        hex_label.set_xalign(1)
        self.hex_entry = Gtk.Entry()
        self.hex_entry.set_max_length(7)
        self.hex_entry.set_width_chars(9)
        self.hex_entry.set_text(to_hex(self.rgb))
        fields.attach(hex_label, 0, 3, 1, 1)
        fields.attach(self.hex_entry, 1, 3, 1, 1)
        right.pack_start(fields, False, False, 0)
        for spin in self.spins:                  # connected last, so filling in the start values says nothing
            spin.connect("value-changed", self.on_spin)
        self.hex_entry.connect("changed", self.on_hex_changed)
        self.hex_entry.connect("activate", lambda *_: self.normalise_hex())
        self.hex_entry.connect("focus-out-event", lambda *_: self.normalise_hex())

    def make_area(self, width, height, draw, kind):
        area = Gtk.DrawingArea()
        area.set_size_request(width, height)
        area.add_events(Gdk.EventMask.BUTTON_PRESS_MASK | Gdk.EventMask.BUTTON_RELEASE_MASK
                        | Gdk.EventMask.POINTER_MOTION_MASK)
        area.connect("draw", draw)
        area.connect("button-press-event", lambda w, e: self.on_press(w, e, kind))
        area.connect("motion-notify-event", lambda w, e: self.on_motion(w, e, kind))
        area.connect("button-release-event", self.on_release)
        return area

    @staticmethod
    def size_of(widget):
        alloc = widget.get_allocation()
        return max(1, alloc.width), max(1, alloc.height)

    def on_draw_sv(self, widget, cr):
        width, height = self.size_of(widget)
        draw_sv_square(cr, width, height, self.h, self.s, self.v)
        return False

    def on_draw_hue(self, widget, cr):
        width, height = self.size_of(widget)
        draw_hue_strip(cr, width, height, self.h)
        return False

    @staticmethod
    def paint_swatch(widget, cr, rgb):
        alloc = widget.get_allocation()
        draw_swatch(cr, alloc.width, alloc.height, tuple(c / 255.0 for c in rgb))
        return False

    # ----- mouse: dragging in the square / on the rainbow bar ---------------------------------------
    def on_press(self, widget, event, kind):
        if event.button != 1:
            return False
        self.drag = kind
        self.drag_to(widget, event)
        return True

    def on_motion(self, widget, event, kind):
        if self.drag != kind:
            return False
        self.drag_to(widget, event)
        return True

    def on_release(self, widget, event):
        self.drag = None
        return True

    def drag_to(self, widget, event):
        width, height = self.size_of(widget)
        x = max(0.0, min(1.0, event.x / width))
        if self.drag == "sv":
            self.s = x
            self.v = 1.0 - max(0.0, min(1.0, event.y / height))
        else:
            self.h = x
        self.rgb = hsv_to_rgb(self.h, self.s, self.v)
        self.push(skip=None)

    # ----- the number boxes and the hex code -------------------------------------------------------
    def on_spin(self, _spin):
        if not self.syncing:
            self.set_from_rgb(tuple(int(spin.get_value()) for spin in self.spins), skip="spin")

    def on_hex_changed(self, entry):
        if self.syncing:
            return
        rgb = parse_hex_colour(entry.get_text())
        if rgb is not None:                      # half-typed codes are simply ignored
            self.set_from_rgb(rgb, skip="hex")

    def normalise_hex(self):
        """Write the code as '#RRGGBB' again (after typing 'abc', or when the box is left)."""
        self.syncing = True
        self.hex_entry.set_text(to_hex(self.rgb))
        self.syncing = False
        return False

    def set_from_rgb(self, rgb, skip):
        self.rgb = tuple(rgb)
        h, s, v = rgb_to_hsv(self.rgb)
        if s > 0 and v > 0:                      # a grey has no hue of its own: keep the bar where it is
            self.h = h
        self.s, self.v = s, v
        self.push(skip)

    def push(self, skip):
        """Show self.rgb in every part of the picker except the box the person is typing in."""
        self.syncing = True
        if skip != "spin":
            for spin, value in zip(self.spins, self.rgb):
                spin.set_value(value)
        if skip != "hex":
            self.hex_entry.set_text(to_hex(self.rgb))
        self.syncing = False
        for area in (self.sv_area, self.hue_area, self.new_area):
            area.queue_draw()
        if self.on_change is not None:
            self.on_change(to_hex(self.rgb))

    def choose(self):
        """Show the picker and wait for it.  Returns the chosen '#RRGGBB', or None if it was cancelled."""
        self.show_all()
        response = self.run()
        result = to_hex(self.rgb) if response == Gtk.ResponseType.OK else None
        self.destroy()
        return result


class VisualSettingsWindow(Gtk.Window):
    """Pieces, board colours, where the engine lines go, and Light / Dark mode.  Every choice is applied
    at once (the main window is behind it, so you can watch), and remembered."""
    PREVIEW = 56

    def __init__(self, app):
        super().__init__(title="Visual Settings", transient_for=app, destroy_with_parent=True)
        watch_titlebar(self)
        self.app = app
        self.syncing = False
        self.set_resizable(False)
        self.set_border_width(18)
        self.set_position(Gtk.WindowPosition.CENTER_ON_PARENT)
        self.connect("destroy", self.on_destroy)
        self.connect("key-press-event", self.on_key)

        grid = Gtk.Grid()
        grid.set_column_spacing(16)
        grid.set_row_spacing(18)
        self.add(grid)

        # Pieces, with a Dragon beside the list as a preview
        grid.attach(self.caption("Pieces:"), 0, 0, 1, 1)
        self.piece_combo = Gtk.ComboBoxText()
        for name in app.piece_set_names:
            self.piece_combo.append_text(name)
        self.piece_combo.set_active(app.piece_set_names.index(app.piece_set_name))
        self.piece_combo.set_valign(Gtk.Align.CENTER)
        self.piece_combo.connect("changed", self.on_piece_changed)
        grid.attach(self.piece_combo, 1, 0, 1, 1)
        self.piece_preview = self.preview_area(self.on_draw_piece)
        grid.attach(self.piece_preview, 2, 0, 1, 1)

        # Board colors: Classic / Green / Blue / Custom (two clickable swatches), with a 4-square preview
        grid.attach(self.caption("Board colors:"), 0, 1, 1, 1)
        scheme_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        scheme_box.set_valign(Gtk.Align.CENTER)
        self.scheme_combo = Gtk.ComboBoxText()
        for _key, name in SCHEME_CHOICES:
            self.scheme_combo.append_text(name)
        self.scheme_combo.set_active([key for key, _name in SCHEME_CHOICES].index(app.board_scheme))
        self.scheme_combo.connect("changed", self.on_scheme_changed)
        scheme_box.pack_start(self.scheme_combo, False, False, 0)
        self.swatch_buttons, self.swatch_areas = {}, {}
        for which, tip in (("light", "Light squares: click to choose a colour"),
                           ("dark", "Dark squares: click to choose a colour")):
            button, area = self.make_swatch(which, tip)
            scheme_box.pack_start(button, False, False, 0)
            self.swatch_buttons[which], self.swatch_areas[which] = button, area
        grid.attach(scheme_box, 1, 1, 1, 1)
        self.board_preview = self.preview_area(self.on_draw_checker)
        grid.attach(self.board_preview, 2, 1, 1, 1)

        # Engine lines: Top or Bottom
        grid.attach(self.caption("Engine lines:"), 0, 2, 1, 1)
        lines_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=16)
        self.radio_top = Gtk.RadioButton.new_with_label_from_widget(None, "Top")
        self.radio_bottom = Gtk.RadioButton.new_with_label_from_widget(self.radio_top, "Bottom")
        self.radio_top.set_tooltip_text("Above the Eval line")
        self.radio_bottom.set_tooltip_text("At the bottom of the window")
        (self.radio_top if app.lines_position == "top" else self.radio_bottom).set_active(True)
        self.radio_top.connect("toggled", lambda b: self.on_lines_position(b, "top"))
        self.radio_bottom.connect("toggled", lambda b: self.on_lines_position(b, "bottom"))
        lines_box.pack_start(self.radio_top, False, False, 0)
        lines_box.pack_start(self.radio_bottom, False, False, 0)
        grid.attach(lines_box, 1, 2, 2, 1)

        # Light / Dark
        grid.attach(self.caption("Appearance:"), 0, 3, 1, 1)
        mode_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=12)
        self.switch = ThemeSwitch(app.theme_name == "light", self.on_switch)
        self.switch.widget.set_valign(Gtk.Align.CENTER)
        self.mode_label = Gtk.Label(label=self.mode_text())
        mode_box.pack_start(self.switch.widget, False, False, 0)
        mode_box.pack_start(self.mode_label, False, False, 0)
        grid.attach(mode_box, 1, 3, 2, 1)

        close = Gtk.Button(label="Close")
        close.set_halign(Gtk.Align.END)
        close.connect("clicked", lambda _b: self.destroy())
        grid.attach(close, 0, 4, 3, 1)

    # ----- small builders ---------------------------------------------------------------------------
    @staticmethod
    def caption(text):
        label = Gtk.Label(label=text)
        label.set_xalign(0)
        label.set_valign(Gtk.Align.CENTER)
        return label

    def preview_area(self, draw):
        area = Gtk.DrawingArea()
        area.set_size_request(self.PREVIEW, self.PREVIEW)
        area.set_valign(Gtk.Align.CENTER)
        area.connect("draw", draw)
        return area

    def make_swatch(self, which, tooltip):
        button = Gtk.Button()
        area = Gtk.DrawingArea()
        area.set_size_request(34, 20)
        area.connect("draw", lambda w, cr: self.on_draw_swatch(w, cr, which))
        button.add(area)
        button.set_tooltip_text(tooltip)
        button.connect("clicked", lambda _b: self.pick_colour(which))
        button.set_no_show_all(True)             # only visible while the board is Custom
        area.show()
        return button, area

    def mode_text(self):
        return "Light Mode" if self.app.theme_name == "light" else "Dark Mode"

    def after_show(self):
        """show_all() skips the swatches (they appear only for Custom), so this sets them up."""
        self.update_swatches()

    def update_swatches(self):
        for button in self.swatch_buttons.values():
            if self.app.board_scheme == CUSTOM:
                button.show()
            else:
                button.hide()

    def refresh_previews(self):
        """The main window changed something: redraw the pictures and make the controls agree."""
        self.syncing = True
        try:
            app = self.app
            if app.piece_set_name in app.piece_set_names:
                self.piece_combo.set_active(app.piece_set_names.index(app.piece_set_name))
            self.scheme_combo.set_active([key for key, _name in SCHEME_CHOICES].index(app.board_scheme))
            (self.radio_top if app.lines_position == "top" else self.radio_bottom).set_active(True)
            self.switch.set_light(app.theme_name == "light")
            self.mode_label.set_text(self.mode_text())
        finally:
            self.syncing = False
        self.update_swatches()
        for area in (self.piece_preview, self.board_preview, *self.swatch_areas.values()):
            area.queue_draw()

    # ----- drawing ---------------------------------------------------------------------------------
    def on_draw_piece(self, widget, cr):
        draw_piece_preview(cr, self.PREVIEW, self.app.board_colours, self.app.piece_images)
        return False

    def on_draw_checker(self, widget, cr):
        colours = self.app.board_colours
        draw_checker(cr, self.PREVIEW, colours["light"], colours["dark"])
        return False

    def on_draw_swatch(self, widget, cr, which):
        light_hex, dark_hex = self.app.current_scheme_hexes()
        alloc = widget.get_allocation()
        draw_swatch(cr, alloc.width, alloc.height, hex_to_unit(light_hex if which == "light" else dark_hex))
        return False

    # ----- the controls ----------------------------------------------------------------------------
    def on_piece_changed(self, combo):
        idx = combo.get_active()
        if not self.syncing and 0 <= idx < len(self.app.piece_set_names):
            self.app.use_piece_set(self.app.piece_set_names[idx])

    def on_scheme_changed(self, combo):
        idx = combo.get_active()
        if not self.syncing and 0 <= idx < len(SCHEME_CHOICES):
            self.app.set_board_scheme(SCHEME_CHOICES[idx][0])
            self.update_swatches()

    def on_lines_position(self, button, position):
        if button.get_active() and not self.syncing:
            self.app.set_lines_position(position)

    def on_switch(self, light):
        self.app.set_theme("light" if light else "dark")
        self.mode_label.set_text(self.mode_text())

    def pick_colour(self, which):
        """Open the colour picker for the light or dark squares of the Custom board."""
        app = self.app
        light_hex, dark_hex = app.current_scheme_hexes()
        old = light_hex if which == "light" else dark_hex
        picker = ColourPickerDialog(
            self, "Light squares" if which == "light" else "Dark squares", old,
            on_change=lambda hex_colour: app.set_custom_colour(which, hex_colour, commit=False))
        chosen = picker.choose()                 # the board followed the picker; Cancel puts the old colour back
        app.set_custom_colour(which, chosen or old, commit=bool(chosen))

    def on_key(self, widget, event):
        if event.keyval == Gdk.KEY_Escape:
            self.destroy()
            return True
        return False

    def on_destroy(self, *_):
        if self.app.visual_win is self:
            self.app.visual_win = None


ENGINE_NAMES = ("dragonanga-engine", "stockfish", "fairy-stockfish")

# ---------------------------------------------------------------------------
# Piece picture sets:  pieces/<set name>/<white|black>-<piece>.png
# ---------------------------------------------------------------------------
TOKENS = "Simple tokens"          # the built-in drawn pieces; always available
DEFAULT_PIECE_SET = TOKENS        # set this to e.g. "Handmade" to start with pictures
PIECE_IMAGE_SCALE = 0.92          # picture size as a fraction of the square
PIECE_WORDS = {e: name.lower().replace(" ", "-") for e, (_, name) in PIECE_DISPLAY.items()}
#   {'P': 'soldier', 'I': 'guard', 'E': 'elephant', 'H': 'horse', 'D': 'dragon',
#    'K': 'queen-fairy', 'C': 'king', 'F': 'fairy', 'M': 'minister'}
ALL_PIECE_KEYS = [(color, word) for color in ("white", "black") for word in PIECE_WORDS.values()]


def piece_key(piece):
    """Board letter (engine letter, upper case = White) -> ('white', 'queen-fairy')."""
    return ("white" if piece.isupper() else "black", PIECE_WORDS.get(piece.upper()))


def find_piece_sets(dirs=None):
    """Scan <dir>/pieces/*/ for picture sets.  Returns {set name: {(color, word): file path}}.

    A set's name is its folder name.  File names are matched loosely: 'White-Queen_Fairy.PNG'
    works as well as 'white-queen-fairy.png'.  Folders without any recognised piece are ignored,
    and a set that lacks some pieces is still listed (the missing ones are drawn as tokens)."""
    sets = {}
    for folder in (dirs if dirs is not None else app_dirs()):
        root = os.path.join(folder, "pieces")
        try:
            names = sorted(os.listdir(root), key=str.lower)
        except OSError:
            continue
        for set_name in names:
            path = os.path.join(root, set_name)
            if set_name in sets or not os.path.isdir(path):
                continue
            files = {}
            for fname in sorted(os.listdir(path)):
                stem, ext = os.path.splitext(fname)
                if ext.lower() != ".png":
                    continue
                key = tuple(re.sub(r"[\s_]+", "-", stem.strip().lower()).split("-", 1))
                if key in ALL_PIECE_KEYS:
                    files[key] = os.path.join(path, fname)
            if files:
                sets[set_name] = files
    return sets


def piece_set_report(sets):
    """Plain-text summary of what find_piece_sets() found, with the missing pieces named."""
    if not sets:
        return "No piece sets found. Expected pieces/<set name>/white-soldier.png etc. next to the app."
    lines = []
    for name, files in sets.items():
        missing = [f"{c}-{w}" for c, w in ALL_PIECE_KEYS if (c, w) not in files]
        status = "complete" if not missing else f"missing {len(missing)}: " + ", ".join(missing)
        lines.append(f"{name}: {len(files)} of {len(ALL_PIECE_KEYS)} pieces, {status}")
    return "\n".join(lines)


class PieceImages:
    """The pictures of one set, ready to draw.  Scaled copies are cached per size so the board
    stays fast and looks sharp at any window size."""

    def __init__(self, files):
        self.files = files
        self.originals = {}   # key -> cairo surface, or None if the file could not be read
        self.scaled = {}      # (key, pixels) -> cairo surface

    def _original(self, key):
        if key not in self.originals:
            surface = None
            path = self.files.get(key)
            if path:
                try:
                    surface = cairo.ImageSurface.create_from_png(path)
                except Exception as e:  # unreadable or not really a PNG
                    print(f"[PIECES] cannot read {path}: {e}")
            self.originals[key] = surface
        return self.originals[key]

    def get(self, piece, pixels):
        """Surface (pixels x pixels, transparent) for a board letter, or None -> draw a token."""
        key = piece_key(piece)
        pixels = max(1, int(pixels))
        hit = self.scaled.get((key, pixels))
        if hit is None:
            src = self._original(key)
            if src is None:
                return None
            w, h = src.get_width(), src.get_height()
            if w <= 0 or h <= 0:
                return None
            scale = pixels / float(max(w, h))      # keeps the aspect ratio of non-square pictures
            hit = cairo.ImageSurface(cairo.FORMAT_ARGB32, pixels, pixels)
            ctx = cairo.Context(hit)
            ctx.translate((pixels - w * scale) / 2.0, (pixels - h * scale) / 2.0)
            ctx.scale(scale, scale)
            ctx.set_source_surface(src, 0, 0)
            ctx.get_source().set_filter(cairo.FILTER_BEST)   # smooth down- and up-scaling
            ctx.paint()
            if len(self.scaled) > 400:
                self.scaled.clear()
            self.scaled[(key, pixels)] = hit
        return hit


def app_dirs():
    """Folders searched for the engine that ships with the app (packaged .exe or plain script)."""
    dirs = []
    if getattr(sys, "frozen", False):                 # PyInstaller build
        dirs.append(getattr(sys, "_MEIPASS", None))   # where bundled files are unpacked
        dirs.append(os.path.dirname(sys.executable))  # next to play_dragonanga.exe
    dirs.append(os.path.dirname(os.path.abspath(__file__)))
    return [d for d in dirs if d]


def find_bundled_engine(dirs=None):
    """Path of an engine shipped with the app, or None.  Looks for dragonanga-engine / stockfish
    (+ .exe on Windows) in the app folder and in an 'engine' sub-folder."""
    suffix = ".exe" if os.name == "nt" else ""
    for folder in (dirs if dirs is not None else app_dirs()):
        for sub in ("", "engine"):
            for name in ENGINE_NAMES:
                path = os.path.join(folder, sub, name + suffix)
                if os.path.isfile(path) and (os.name == "nt" or os.access(path, os.X_OK)):
                    return path
    return None


def pick_engine_executable():
    dialog = Gtk.FileChooserDialog(
        title="Select the Dragonanga engine (your compiled Fairy-Stockfish)",
        action=Gtk.FileChooserAction.OPEN,
    )
    dialog.add_buttons(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK)
    resp = dialog.run()
    path = dialog.get_filename() if resp == Gtk.ResponseType.OK else None
    dialog.destroy()
    return path


def show_error(text, parent=None):
    extra = {"transient_for": parent} if parent is not None else {}
    dialog = Gtk.MessageDialog(
        message_type=Gtk.MessageType.ERROR, buttons=Gtk.ButtonsType.CLOSE, text=text, **extra)
    watch_titlebar(dialog)
    dialog.run()
    dialog.destroy()


if __name__ == "__main__":
    if "--check-pieces" in sys.argv:       # no window: just report what is in the pieces/ folder
        print(piece_set_report(find_piece_sets()))
        sys.exit(0)
    # Engine: a path given on the command line or in DRAGONANGA_ENGINE, else the one shipped with
    # the app, else ask.
    exe = (sys.argv[1] if len(sys.argv) > 1 else os.environ.get("DRAGONANGA_ENGINE")) \
        or find_bundled_engine() or pick_engine_executable()
    if exe and os.path.isfile(exe):
        try:
            win = DragonangaWindow(exe)
        except OSError as e:
            show_error(f"The engine could not be started:\n{exe}\n\n{e}")
        else:
            win.show_all()
            Gtk.main()
    elif exe:
        show_error(f"Engine not found:\n{exe}")