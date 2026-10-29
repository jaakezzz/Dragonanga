#!/bin/sh
# Starts Dragonanga. Needs Python 3 with GTK 3 (PyGObject) and pycairo from your distribution.
here="$(cd "$(dirname "$0")" && pwd)"

if ! python3 -c "import gi; gi.require_version('Gtk', '3.0'); from gi.repository import Gtk; import cairo" 2>/dev/null; then
    cat >&2 <<'MSG'
Dragonanga needs Python 3 with GTK 3 and pycairo. Install them with your package manager:

  Debian / Ubuntu / Mint:  sudo apt install python3-gi python3-gi-cairo python3-cairo gir1.2-gtk-3.0
  Fedora:                  sudo dnf install python3-gobject python3-cairo gtk3
  Arch / Manjaro:          sudo pacman -S python-gobject python-cairo gtk3
  openSUSE:                sudo zypper install python3-gobject python3-gobject-Gdk python3-cairo typelib-1_0-Gtk-3_0

then run this script again.
MSG
    exit 1
fi

exec python3 "$here/play_dragonanga.py" "$@"
