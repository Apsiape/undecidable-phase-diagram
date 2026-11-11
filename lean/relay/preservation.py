"""Proof-preservation census (run in WSL with python3 -I -B).

Method. For every original Lean file (commit f475c20, original/) and its ported counterpart (project/):
remove comments (nested block comments `/- ... -/`, including doc comments, and `--` line comments,
string literals respected) and split the text into top-level declaration blocks at lines that start
(after optional attributes / modifiers) with a declaration keyword. A theorem/lemma block is split into
its header (from the keyword to the first `:=` at bracket depth 0, or to the first equation line `|`)
and its proof (the rest of the block). Headers are compared after whitespace normalization; every other
declaration (def, abbrev, instance, structure, inductive, class, ...) is compared IN FULL after
normalization, so any change in a definition body is reported as well. Blocks are matched by
(file, keyword, name, occurrence index).
"""
from pathlib import Path
import hashlib, json, re, sys

D = Path('/opt/undecidable-phase-diagram-arxiv-2026-11-11')
OLD, NEW = D / 'original', D / 'project'
KW = r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example|noncomputable\s+def|irreducible_def)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example)\b\s*([^\s:({\[⦃]*)')


def strip_comments(t):
    out, i, n, depth = [], 0, len(t), 0
    while i < n:
        if depth == 0 and t.startswith('"', i):
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == '\\' else 1
            out.append(t[i:j + 1]); i = j + 1; continue
        if t.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and t.startswith('-/', i):
            depth -= 1; i += 2
            if depth == 0: out.append(' ')
            continue
        if depth:
            if t[i] == '\n': out.append('\n')
            i += 1; continue
        if t.startswith('--', i):
            j = t.find('\n', i)
            i = n if j < 0 else j
            continue
        out.append(t[i]); i += 1
    return ''.join(out)


def norm(s):
    return ' '.join(s.split())


def blocks(text):
    t = strip_comments(text)
    lines = t.split('\n')
    starts = []
    for k, l in enumerate(lines):
        m = DECL.match(l)
        if m:
            starts.append((k, m.group(1), m.group(2)))
    res = []
    for idx, (k, kw, name) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
        # stop the block at the next top-level command that is not a declaration
        body_lines = lines[k:end]
        for j in range(1, len(body_lines)):
            if re.match(r'^(end|namespace|section|open|set_option|variable|universe|#|attribute|noncomputable section|/-!|run_cmd|export|omit|include)\b', body_lines[j]):
                body_lines = body_lines[:j]; break
        block = '\n'.join(body_lines)
        res.append({'line': k + 1, 'kw': kw, 'name': name, 'text': block})
    return res


def split_header(block):
    depth, i, t = 0, 0, block
    opens, closes = '([{⟨⦃', ')]}⟩⦄'
    lines = t.split('\n')
    pos = 0
    for li, l in enumerate(lines):
        if li > 0 and depth == 0 and re.match(r'^\s*\|', l):
            return t[:pos], t[pos:]
        for ci, c in enumerate(l):
            if c in opens: depth += 1
            elif c in closes: depth = max(0, depth - 1)
            elif depth == 0 and l.startswith(':=', ci):
                return t[:pos + ci], t[pos + ci:]
        pos += len(l) + 1
    return t, ''


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


files = sorted(p.relative_to(OLD) for p in OLD.rglob('*.lean'))
theorems, others, changed_files, problems = [], [], [], []
for rel in files:
    old = (OLD / rel).read_text(encoding='utf-8')
    newp = NEW / rel
    if not newp.exists():
        problems.append({'file': str(rel), 'problem': 'missing in port'}); continue
    new = newp.read_text(encoding='utf-8')
    if old != new: changed_files.append(str(rel))
    ob, nb = blocks(old), blocks(new)
    def key(bs):
        seen, out = {}, {}
        for b in bs:
            k = (b['kw'], b['name']); c = seen.get(k, 0); seen[k] = c + 1
            out[(b['kw'], b['name'], c)] = b
        return out
    ok, nk = key(ob), key(nb)
    if set(ok) != set(nk):
        problems.append({'file': str(rel), 'problem': 'declaration sets differ',
                         'only_old': sorted(map(str, set(ok) - set(nk))), 'only_new': sorted(map(str, set(nk) - set(ok)))})
    for k in ok:
        if k not in nk: continue
        o, n = ok[k], nk[k]
        if k[0] in ('theorem', 'lemma'):
            oh, op = split_header(o['text']); nh, np_ = split_header(n['text'])
            rec = {'file': str(rel), 'source_name': k[1], 'occurrence': k[2], 'old_line': o['line'], 'new_line': n['line'],
                   'statement_sha256': sha(norm(oh)), 'statement_unchanged': norm(oh) == norm(nh),
                   'old_proof_block_sha256': sha(norm(op)), 'new_proof_block_sha256': sha(norm(np_)),
                   'proof_block_changed': norm(op) != norm(np_)}
            theorems.append(rec)
        else:
            oh, ob_ = split_header(o['text']); nh, nb_ = split_header(n['text'])
            others.append({'file': str(rel), 'kind': k[0], 'source_name': k[1], 'occurrence': k[2], 'old_line': o['line'],
                           'new_line': n['line'], 'unchanged_in_full': norm(o['text']) == norm(n['text']),
                           'header_unchanged': norm(oh) == norm(nh), 'body_unchanged': norm(ob_) == norm(nb_),
                           'old_header': norm(oh) if norm(oh) != norm(nh) else None,
                           'new_header': norm(nh) if norm(oh) != norm(nh) else None,
                           'sha256': sha(norm(o['text']))})
st_old = (OLD / 'UndecidablePhaseDiagram/Statements.lean').read_bytes()
st_new = (NEW / 'UndecidablePhaseDiagram/Statements.lean').read_bytes()
rec = {
    'original_commit': 'f475c200b1fe55d01dcb1e582bd910fcc01ab2bc',
    'lean': '4.35.0', 'mathlib_commit': '56a005855ea17e0b0958f73ec801ae140b0a1679',
    'statements_lean_byte_identical': st_old == st_new,
    'statements_lean_sha256': hashlib.sha256(st_new).hexdigest(),
    'original_lean_files': len(files),
    'changed_original_lean_files': changed_files,
    'theorems_checked': len(theorems),
    'theorem_statements_changed': [t for t in theorems if not t['statement_unchanged']],
    'changed_theorem_proof_blocks': sum(t['proof_block_changed'] for t in theorems),
    'other_declarations_checked': len(others),
    'other_declarations_changed': [o for o in others if not o['unchanged_in_full']],
    'problems': problems,
    'method': __doc__.strip(),
    'theorems': theorems,
    'other_declarations': others,
}
out = Path(sys.argv[1]) if len(sys.argv) > 1 else D / 'evidence' / 'PROOF-PRESERVATION.json'
out.write_text(json.dumps(rec, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps({k: (v if not isinstance(v, list) else (len(v) if len(v) > 8 else v)) for k, v in rec.items() if k not in ('method',)}, indent=1, ensure_ascii=False)[:6000])
