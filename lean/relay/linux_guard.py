from pathlib import Path
import os,subprocess,time,signal

def guarded_run(command,**kwargs):
 start=time.monotonic();peak=0;peak_vms=0;limit_hit=False
 p=subprocess.Popen(command,**kwargs)
 while p.poll() is None:
  entries={}
  for d in Path('/proc').iterdir():
   if not d.name.isdigit():continue
   try:
    fields=dict(line.split(':',1) for line in (d/'status').read_text().splitlines() if ':' in line)
    entries[int(d.name)]=(int(fields['PPid']),int(fields.get('VmRSS','0 kB').split()[0])*1024,int(fields.get('VmSize','0 kB').split()[0])*1024)
   except (OSError,KeyError,ValueError):pass
  ids={p.pid};changed=True
  while changed:
   new={n for n,v in entries.items() if v[0] in ids};changed=not new<=ids;ids|=new
  rss=sum(entries.get(n,(0,0,0))[1] for n in ids);vms=sum(entries.get(n,(0,0,0))[2] for n in ids)
  peak=max(peak,rss);peak_vms=max(peak_vms,vms)
  if rss>=9000000000:
   limit_hit=True
   for n in ids:
    try:os.kill(n,signal.SIGKILL)
    except ProcessLookupError:pass
   break
  time.sleep(.1)
 rc=p.wait()
 return {'exit':rc,'seconds':round(time.monotonic()-start,3),'peak_tree_rss_bytes':peak,'peak_tree_vms_bytes':peak_vms,'stop_rss_bytes':9000000000,'memory_stop':limit_hit}
