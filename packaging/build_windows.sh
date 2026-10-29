#!/usr/bin/env bash
# Builds Dragonanga-windows-x64.zip.  Run it in an MSYS2 "MINGW64" shell (not UCRT64 / MSYS).
#
# 1. Build the engine in the same shell.  COMP=mingw already links statically:
#      cd Fairy-Stockfish/src
#      make -j build ARCH=x86-64-modern COMP=mingw largeboards=no
#      strip stockfish.exe
# 2. From the folder that contains play_dragonanga.py:
#      packaging/build_windows.sh /path/to/Fairy-Stockfish/src/stockfish.exe
set -euo pipefail
ENGINE="${1:?usage: build_windows.sh /path/to/stockfish.exe}"
cd "$(dirname "$0")/.."

# the engine must not need MinGW DLLs (they are not on a normal Windows PC)
if objdump -p "$ENGINE" | grep -i "DLL Name" | grep -iE "libstdc\+\+|libgcc|libwinpthread"; then
    echo "The engine needs MinGW DLLs. Rebuild it with COMP=mingw (static)." >&2; exit 1
fi

# build tools: Python, GTK 3 and PyGObject from MSYS2; PyInstaller from pip (there is no MSYS2 package
# for it).  gcc is needed because pip compiles PyInstaller's small launcher on MSYS2.
pacman -S --needed --noconfirm \
    mingw-w64-x86_64-python mingw-w64-x86_64-python-pip mingw-w64-x86_64-gcc \
    mingw-w64-x86_64-python-gobject mingw-w64-x86_64-python-cairo mingw-w64-x86_64-gtk3
python -m pip install --break-system-packages --upgrade pyinstaller

# everything the build produces goes into release/ (ignored by git)
OUT=release
mkdir -p "$OUT"
rm -rf "$OUT/work" "$OUT/dist" "$OUT/play_dragonanga.spec"   # keeps earlier zips in release/
python -m PyInstaller --noconfirm --windowed --name play_dragonanga \
    --workpath "$OUT/work" --distpath "$OUT/dist" --specpath "$OUT" play_dragonanga.py

# the app looks for the engine next to play_dragonanga.exe
cp "$ENGINE" "$OUT/dist/play_dragonanga/dragonanga-engine.exe"
cp packaging/README_windows.txt "$OUT/dist/play_dragonanga/README.txt"
cp packaging/COPYING.txt "$OUT/dist/play_dragonanga/"

NAME=Dragonanga-windows-x64
(cd "$OUT/dist" && python -m zipfile -c "../$NAME.zip" play_dragonanga)
echo "Built $OUT/$NAME.zip - test it on a PC (or Windows Sandbox) without MSYS2 before sharing."
