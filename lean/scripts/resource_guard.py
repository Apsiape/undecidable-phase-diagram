"""Serial, memory-capped build, axiom audit, and sandboxed comparator for Theorem A.
No source downloads or dependency edits. Use cached pinned packages already installed.
"""
import argparse,ctypes,datetime,hashlib,json,os,pathlib,re,shutil,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parent
CAP=10_000_000_000
PIN='eb6cafb7290e8bd5f2937522d8d804f58f02bafc'

PRIMITIVE_TARGETS = ['Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod','Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight','String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char','optParam','autoParam','semiOutParam','outParam']
def export_targets(cfg):
    return ['Quot','Quot.mk','Quot.lift','Quot.ind']+cfg['theorem_names']+cfg['permitted_axioms']+PRIMITIVE_TARGETS

def comparator_lookup_path(env):
    # Pinned Lake's context does Unix `which git`/`which env` lookups even for
    # two supplied exports. No git process or dependency resolution is run.
    if os.name=='nt':
        base=pathlib.Path(os.environ.get('ProgramFiles',str(pathlib.Path(sys.executable).anchor))) / 'Git'
        additions=[p for p in (base/'usr/bin',base/'cmd') if p.is_dir()]
        env['PATH']=os.pathsep.join(map(str,additions))+os.pathsep+env['PATH']


def memory_cap():
    if os.name!='nt':
        # Bound resident memory, not the address space occupied by mapped proof files.
        import resource,threading,signal
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
        state={'peak':0}
        root_pid=os.getpid()
        def watch():
            while True:
                entries={}
                for d in pathlib.Path('/proc').iterdir():
                    if not d.name.isdigit():continue
                    try:
                        fields=dict(line.split(':',1) for line in (d/'status').read_text().splitlines() if ':' in line)
                        entries[int(d.name)]=(int(fields['PPid']),int(fields.get('VmRSS','0 kB').split()[0])*1024)
                    except (OSError,KeyError,ValueError):pass
                ids={root_pid};changed=True
                while changed:
                    new_ids={n for n,v in entries.items() if v[0] in ids};changed=not new_ids<=ids;ids|=new_ids
                rss=sum(entries.get(n,(0,0))[1] for n in ids);state['peak']=max(state['peak'],rss)
                if rss>=min(CAP-100000000,9000000000):
                    for n in ids-{root_pid}:
                        try:os.kill(n,signal.SIGKILL)
                        except ProcessLookupError:pass
                    os.kill(root_pid,signal.SIGTERM)
                    return
                time.sleep(.25)
        threading.Thread(target=watch,daemon=True).start()
        return lambda:state['peak']
    from ctypes import wintypes as w
    class Basic(ctypes.Structure):
        _fields_=[('PerProcessUserTimeLimit',ctypes.c_int64),('PerJobUserTimeLimit',ctypes.c_int64),('LimitFlags',w.DWORD),('MinimumWorkingSetSize',ctypes.c_size_t),('MaximumWorkingSetSize',ctypes.c_size_t),('ActiveProcessLimit',w.DWORD),('Affinity',ctypes.c_size_t),('PriorityClass',w.DWORD),('SchedulingClass',w.DWORD)]
    class IO(ctypes.Structure):
        _fields_=[(n,ctypes.c_uint64) for n in ('ReadOperationCount','WriteOperationCount','OtherOperationCount','ReadTransferCount','WriteTransferCount','OtherTransferCount')]
    class Extended(ctypes.Structure):
        _fields_=[('BasicLimitInformation',Basic),('IoInfo',IO),('ProcessMemoryLimit',ctypes.c_size_t),('JobMemoryLimit',ctypes.c_size_t),('PeakProcessMemoryUsed',ctypes.c_size_t),('PeakJobMemoryUsed',ctypes.c_size_t)]
    k=ctypes.WinDLL('kernel32',use_last_error=True)
    k.CreateJobObjectW.argtypes=[ctypes.c_void_p,w.LPCWSTR];k.CreateJobObjectW.restype=w.HANDLE
    k.SetInformationJobObject.argtypes=[w.HANDLE,ctypes.c_int,ctypes.c_void_p,w.DWORD];k.SetInformationJobObject.restype=w.BOOL
    k.AssignProcessToJobObject.argtypes=[w.HANDLE,w.HANDLE];k.AssignProcessToJobObject.restype=w.BOOL
    k.GetCurrentProcess.restype=w.HANDLE
    k.QueryInformationJobObject.argtypes=[w.HANDLE,ctypes.c_int,ctypes.c_void_p,w.DWORD,ctypes.c_void_p];k.QueryInformationJobObject.restype=w.BOOL
    job=k.CreateJobObjectW(None,None);lim=Extended();lim.BasicLimitInformation.LimitFlags=0x200;lim.JobMemoryLimit=CAP
    if not job or not k.SetInformationJobObject(job,9,ctypes.byref(lim),ctypes.sizeof(lim)) or not k.AssignProcessToJobObject(job,k.GetCurrentProcess()):raise ctypes.WinError(ctypes.get_last_error())
    def peak():
        stat=Extended()
        if not k.QueryInformationJobObject(job,9,ctypes.byref(stat),ctypes.sizeof(stat),None):raise ctypes.WinError(ctypes.get_last_error())
        return stat.PeakJobMemoryUsed
    return peak

