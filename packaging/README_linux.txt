Dragonanga - play and analyse (Linux, 64-bit)
=============================================

1. Install the GUI libraries once (the launcher prints these commands too if they are missing):
     Debian / Ubuntu / Mint:  sudo apt install python3-gi python3-gi-cairo python3-cairo gir1.2-gtk-3.0
     Fedora:                  sudo dnf install python3-gobject python3-cairo gtk3
     Arch / Manjaro:          sudo pacman -S python-gobject python-cairo gtk3
2. Unpack this archive anywhere and run:   ./play_dragonanga.sh

The Dragonanga engine (dragonanga-engine) is included. It is a statically linked 64-bit build of
Fairy-Stockfish with the Dragonanga rules and needs a CPU with SSE4.1 and POPCNT (any x86-64 CPU
from about 2009 on). If you prefer your own engine build, start with:
     ./play_dragonanga.sh /path/to/your/engine

Licence
-------
The engine is a modified Fairy-Stockfish, released under the GNU General Public License v3
(COPYING.txt). Its source code: https://github.com/jaakezzz/Fairy-Stockfish/tree/Dragonanga-Advanced
