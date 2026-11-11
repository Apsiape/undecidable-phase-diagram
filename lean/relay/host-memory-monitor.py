"""Windows host-memory heartbeat for the WSL build guards (run on Windows with python -I -B).

Every 2 s it writes {utc_epoch, available_bytes, minimum_observed_bytes, total_bytes} (GlobalMemoryStatusEx
ullAvailPhys / ullTotalPhys) atomically to project/.host-memory.json inside the WSL workspace. The serial
replay, check and run scripts refuse to start a Lean/lake/export/kernel process unless the heartbeat is
fresh (< 20 s) and both it and Linux MemAvailable are >= 8 GiB. It exits by itself when the file
project/.host-memory.stop exists or after --max-seconds (default 6 h), so it can never be left running.
(Written for this relay; the forgetting relay's monitor was not copied.)
"""
import argparse, ctypes, json, os, sys, time
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('--project', default=r'\\wsl.localhost\lean-comparator\opt\undecidable-phase-diagram-arxiv-2026-11-11\project')
ap.add_argument('--max-seconds', type=float, default=6 * 3600)
ap.add_argument('--interval', type=float, default=2.0)
a = ap.parse_args()
P = Path(a.project)
out = P / '.host-memory.json'
tmp = P / '.host-memory.tmp'
stop = P / '.host-memory.stop'


class MEMORYSTATUSEX(ctypes.Structure):
    _fields_ = [('dwLength', ctypes.c_ulong), ('dwMemoryLoad', ctypes.c_ulong)] + [
        (k, ctypes.c_ulonglong) for k in ['ullTotalPhys', 'ullAvailPhys', 'ullTotalPageFile', 'ullAvailPageFile',
                                          'ullTotalVirtual', 'ullAvailVirtual', 'ullAvailExtendedVirtual']]


def status():
    m = MEMORYSTATUSEX()
    m.dwLength = ctypes.sizeof(m)
    if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m)):
        raise ctypes.WinError()
    return m.ullAvailPhys, m.ullTotalPhys


start = time.monotonic()
minimum = None
while time.monotonic() - start < a.max_seconds:
    if stop.exists():
        break
    avail, total = status()
    minimum = avail if minimum is None else min(minimum, avail)
    rec = {'utc_epoch': time.time(), 'available_bytes': avail, 'minimum_observed_bytes': minimum, 'total_bytes': total}
    try:
        tmp.write_text(json.dumps(rec))
        os.replace(tmp, out)
    except OSError as e:
        print('write failed', e, file=sys.stderr, flush=True)
    time.sleep(a.interval)
print('monitor stopped; minimum observed', minimum, flush=True)
