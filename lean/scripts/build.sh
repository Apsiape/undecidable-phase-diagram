#!/usr/bin/env bash
# Serial replay of this project's modules (scripts/modules.json) against the vendored pinned
# dependencies: one lean process at a time, -j1 -M6144, 1800 s per module, refuses below 8 GiB
# available (Linux MemAvailable and the host-memory heartbeat .host-memory.json), process-tree cap.
# Usage: scripts/build.sh [Module.Path ...]
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec "${PYTHON:-python3}" -I -B scripts/replay.py --resume "$@"
