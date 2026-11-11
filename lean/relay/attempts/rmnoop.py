"""Remove no-op `simp only` / `dsimp only` occurrences at given (line, col) positions (1-based line, 0-based col).
usage: python3 rmnoop.py FILE line:col [line:col ...]"""
import sys,re
from pathlib import Path
p=Path(sys.argv[1]); lines=p.read_text(encoding='utf-8').split('\n')
pos=sorted([tuple(map(int,a.split(':'))) for a in sys.argv[2:]],reverse=True)
for ln,col in pos:
    l=lines[ln-1]
    m=re.match(r'(simp only|dsimp only|simp)(\s*;\s*|\s*<;>\s*)?',l[col:])
    assert m, (ln,col,l)
    tok=m.group(1)
    rest=l[col+m.end():]
    if l[:col].strip()=='' and rest.strip()=='' :
        del lines[ln-1]; print('deleted line',ln,repr(l)); continue
    assert m.group(2) is not None, ('no separator',ln,l)
    lines[ln-1]=l[:col]+rest; print('edited',ln,repr(l),'->',repr(lines[ln-1]))
p.write_text('\n'.join(lines),encoding='utf-8')
