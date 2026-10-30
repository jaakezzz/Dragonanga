#!/usr/bin/env bash
# Builds Dragonanga-linux-x86_64.tar.gz.
#
# 1. Build a static engine from your Fairy-Stockfish source (on Linux):
#      cd Fairy-Stockfish/src
#      make -j build ARCH=x86-64-modern COMP=gcc largeboards=no EXTRALDFLAGS=-static
#      strip stockfish
# 2. From the folder that contains play_dragonanga.py:
#      packaging/build_linux.sh /path/to/Fairy-Stockfish/src/stockfish
set -euo pipefail
ENGINE="${1:?usage: build_linux.sh /path/to/static/engine}"
cd "$(dirname "$0")/.."

# the engine must run on machines that do not have our libraries
if ldd "$ENGINE" 2>&1 | grep -q "=>"; then
    echo "The engine is dynamically linked:" >&2; ldd "$ENGINE" >&2
    echo "Rebuild it with EXTRALDFLAGS=-static" >&2; exit 1
fi

OUT=release   # build output goes here (ignored by git)
NAME=Dragonanga-linux-x86_64
mkdir -p "$OUT"
rm -rf "$OUT/$NAME" "$OUT/$NAME.tar.gz"
mkdir "$OUT/$NAME"
cp play_dragonanga.py "$OUT/$NAME/"
cp packaging/play_dragonanga.sh "$OUT/$NAME/"
cp "$ENGINE" "$OUT/$NAME/dragonanga-engine"
cp packaging/README_linux.txt "$OUT/$NAME/README.txt"
cp packaging/COPYING.txt "$OUT/$NAME/"
# piece picture sets (the app looks for a pieces/ folder next to play_dragonanga.py)
if [ -d pieces ]; then cp -r pieces "$OUT/$NAME/pieces"; fi
chmod +x "$OUT/$NAME/play_dragonanga.sh" "$OUT/$NAME/dragonanga-engine"
tar czf "$OUT/$NAME.tar.gz" -C "$OUT" "$NAME"
rm -rf "$OUT/$NAME"
echo "Built $OUT/$NAME.tar.gz"
