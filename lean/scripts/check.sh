#!/usr/bin/env bash
# Elaborate ONE Lean file without writing an .olean, under the guards of build.sh: refuses below
# 8 GiB available (Linux MemAvailable and the fresh host-memory heartbeat), memory cap (default
# 4500 MB) and wall-clock limit (default 600 s).
# Usage: scripts/check.sh FILE [MEM_MB] [SECS]
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$here/env.sh"
export PATH="$PROJ/../toolchain/bin:$PATH"
f="$1"; mem="${2:-4500}"; secs="${3:-600}"
g=$(python3 -I -B -c "
import json,time
info=dict((k,int(v.split()[0])*1024) for k,v in (x.split(':',1) for x in open('/proc/meminfo').read().splitlines()))
h=json.load(open('$PROJ/.host-memory.json'))
print(0 if time.time()-h['utc_epoch']>20 else min(info['MemAvailable'],h['available_bytes'])//1024**3)")
if [ "$g" -lt 8 ]; then echo "ABORT: only ${g} GiB available (< 8 GiB) or stale heartbeat"; exit 3; fi
echo "== check $f (available ${g} GiB, cap ${mem} MB, ${secs} s)"
start=$(date +%s)
timeout -k 5 "$secs" lean -j1 -M "$mem" "$f"
echo "   ok in $(( $(date +%s) - start ))s"
