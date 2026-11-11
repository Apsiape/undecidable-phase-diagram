"""Serial Lean source replay with memory floor, process-tree cap and digest receipts.
(Adapted from the forgetting relay, /opt/forgetting-arxiv-2026-11-10/project/scripts/replay.py.)"""
from pathlib import Path
import os,sys,re,json,hashlib,argparse,subprocess,time,signal,threading,shutil
P=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--resume',action='store_true');ap.add_argument('--lean-bin',type=Path);ap.add_argument('modules',nargs='*');A=ap.parse_args()
W=P/'.lake/replay';W.mkdir(parents=True,exist_ok=True)
T=A.lean_bin or Path(os.environ.get('UPD_LEAN_BIN',str(P.parent/'toolchain/bin')))
if not (T/('lean.exe' if os.name=='nt' else 'lean')).is_file():T=Path(shutil.which('lean')).parent
lean=T/('lean.exe' if os.name=='nt' else 'lean')
packages=[P]+sorted(p for p in (P/'vendor').iterdir() if p.is_dir())
env=os.environ.copy();env.update({'PATH':str(T)+os.pathsep+env.get('PATH',''),'LEAN_PATH':os.pathsep.join(str(p/'.lake/build/lib/lean') for p in packages),'LEAN_SRC_PATH':os.pathsep.join(map(str,packages)),'LEAN_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'})
for k in ['TMPDIR','TMP','TEMP','LAKE_CACHE_DIR','MATHLIB_CACHE_DIR']:
 d=W/k;d.mkdir(exist_ok=True);env[k]=str(d)
# The imported helper enforces a Windows Job Object or Linux process-tree RSS ceiling.
import importlib.util
spec=importlib.util.spec_from_file_location('resource_guard',P/'scripts/resource_guard.py');guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard);guard.CAP=9_900_000_000;get_peak=guard.memory_cap()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
# Per-module Lean options (Lean 4.35 compatibility). Statements.lean is frozen (byte-identical,
# sha256 ef3ebe7f...). Its ten enumeration types use Mathlib's `deriving Fintype`, whose generated
# `complete` proof (`rw [Finset.mem_mk, ...]`) fails under Lean 4.35's default
# `backward.isDefEq.respectTransparency = true`; Mathlib at the pin sets this core option to `false`
# for the same derivation (MathlibTest/DeriveFintype.lean, Mathlib/Basic/Sign/Defs.lean). The option
# restores the pre-4.35 unifier behaviour during elaboration only; the kernel is unaffected. The file
# is compiled unchanged with the option set for the whole file (`-D`).
MODULE_OPTIONS={'UndecidablePhaseDiagram.Statements':['-Dbackward.isDefEq.respectTransparency=false']}
def free_bytes():
 if os.name=='nt':
  import ctypes
  class Memory(ctypes.Structure):_fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[(k,ctypes.c_ulonglong) for k in ['totalPhys','availPhys','totalPage','availPage','totalVirtual','availVirtual','availExtended']]
  m=Memory();m.length=ctypes.sizeof(m);ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m));return m.availPhys
 info=dict((k,int(v.split()[0])*1024) for k,v in (x.split(':',1) for x in Path('/proc/meminfo').read_text().splitlines()))
 host=json.loads((P/'.host-memory.json').read_text())
 if time.time()-host['utc_epoch']>20:raise RuntimeError('Host memory monitor heartbeat is stale')
 return min(info['MemAvailable'],host['available_bytes'])
if free_bytes()<8*1024**3:raise RuntimeError('Refusing build: below 8 GiB available physical memory')
version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip();assert '4.35.0' in version and 'eb6cafb7290e' in version,version
mods=A.modules or json.loads((P/'scripts/modules.json').read_text())+['Challenge','Solution','Audit']
seen=set();ordered=[]
def paths(n):
 rel=Path(n.replace('.','/'));return next(((p,p/rel.with_suffix('.lean'),p/'.lake/build/lib/lean'/rel.with_suffix('.olean')) for p in packages if (p/rel.with_suffix('.lean')).is_file()),None)
def visit(n):
 if n in seen:return
 seen.add(n);found=paths(n)
 if found is None:return
 pkg,src,obj=found
 if pkg!=P and obj.exists():return
 for dep in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([\w.]+)',src.read_text(encoding='utf-8'),re.M):visit(dep)
 ordered.append((n,pkg,src,obj))
for n in mods:visit(n)
cachepath=W/'completed.json';cache=json.loads(cachepath.read_text()) if A.resume and cachepath.exists() else {};records=[]
for n,pkg,src,obj in ordered:
 imports={}
 for dep in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([\w.]+)',src.read_text(encoding='utf-8'),re.M):
  d=paths(dep)
  if d and d[2].exists():imports[dep]=sha(d[2])
 sig={'source':sha(src),'imports':imports}
 if n in MODULE_OPTIONS:sig['options']=MODULE_OPTIONS[n]
 if A.resume and obj.exists() and cache.get(n)==sig:continue
 available=free_bytes()
 if available<8*1024**3:raise RuntimeError(f'Refusing {n}: only {available} available (<8 GiB)')
 obj.parent.mkdir(parents=True,exist_ok=True);log=W/(n+'.log')
 cmd=[str(lean),'-j1','-M6144',*MODULE_OPTIONS.get(n,[]),'-o',str(obj),'-i',str(obj.with_suffix('.ilean')),str(src.relative_to(pkg))]
 start=time.monotonic();print('BUILD',n,'free_GiB',round(available/1024**3,2),flush=True)
 with log.open('wb') as f:
  proc=subprocess.Popen(cmd,cwd=pkg,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=os.name!='nt')
  try:rc=proc.wait(timeout=1800)
  except subprocess.TimeoutExpired:
   if os.name!='nt':os.killpg(proc.pid,signal.SIGKILL)
   else:proc.kill()
   rc=124
 record={'module':n,'exit':rc,'seconds':round(time.monotonic()-start,3),'peak_tree_bytes':get_peak(),'free_before_bytes':available,'command':cmd,'log_sha256':sha(log)};records.append(record)
 print('RESULT',n,rc,record['seconds'],'s; peak',round(get_peak()/1024**3,3),'GiB',flush=True)
 (W/'latest.json').write_text(json.dumps({'lean':version,'records':records,'limit_bytes':9_900_000_000},indent=2)+'\n')
 with (W/'history.ndjson').open('a') as f:f.write(json.dumps(record)+'\n')
 if rc:
  print(log.read_text(encoding='utf-8',errors='replace')[-25000:],flush=True);sys.exit(rc)
 cache[n]=sig;cachepath.write_text(json.dumps(cache,indent=2)+'\n')
 if n=='Audit':shutil.copy2(log,P/'AXIOMS.txt')
print('REPLAY PASS',len(ordered),'reachable modules; peak',get_peak(),flush=True)
