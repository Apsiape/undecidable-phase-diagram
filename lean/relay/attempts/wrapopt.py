"""Run the proofs of the named theorems under `set_option backward.isDefEq.respectTransparency false in`
at term level: `... := by` becomes `... :=\n  set_option backward.isDefEq.respectTransparency false in by`.
usage: python3 wrapopt.py FILE name [name ...]   (name = the identifier after `theorem`)"""
import sys,re
from pathlib import Path
p=Path(sys.argv[1]); t=p.read_text(encoding='utf-8')
for name in sys.argv[2:]:
    m=re.search(r'^(theorem|lemma) '+re.escape(name)+r'\b',t,re.M)
    assert m,(name,'not found')
    # find the first ':= by' at end of a line after the header start
    k=t.find(':= by\n',m.start())
    nxt=re.search(r'^(theorem|lemma|def|instance|abbrev|/--)',t[m.end():],re.M)
    assert k>=0 and (nxt is None or k<m.end()+nxt.start()),(name,'no := by')
    t=t[:k]+':=\n  set_option backward.isDefEq.respectTransparency false in by\n'+t[k+len(':= by\n'):]
    print('wrapped',name)
p.write_text(t,encoding='utf-8')
