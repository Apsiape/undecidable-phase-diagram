"""Generate Challenge.lean from the frozen statement files (run in WSL with python3 -I -B).

Challenge.lean imports only Mathlib (the Mathlib imports of Statements.lean and Hypotheses.lean), copies
the text of Statements.lean and of Hypotheses.lean after their import blocks byte for byte, and states the
three final theorems with `sorry`. As in the forgetting relay, `run_cmd ... setMainModule` before each copy
makes generated/private names coincide with those of the development. Statements.lean is compiled in the
development with `-Dbackward.isDefEq.respectTransparency=false` (scripts/replay.py, MODULE_OPTIONS), so its
copy here is elaborated with the same option set (and reset to the default before the Hypotheses copy).
The script re-extracts the copies from the generated file and checks them against the sources.
"""
from pathlib import Path
import hashlib, json, re, sys

D = Path('/opt/undecidable-phase-diagram-arxiv-2026-11-11')
SRC = D / 'project' / 'UndecidablePhaseDiagram'
ORIG = D / 'original' / 'UndecidablePhaseDiagram'


def split(text):
    lines = text.split('\n')
    i = next(k for k, l in enumerate(lines) if l.startswith('import '))
    j = i
    while j < len(lines) and lines[j].startswith('import '):
        j += 1
    return '\n'.join(lines[:i]), lines[i:j], '\n'.join(lines[j:])


st = (SRC / 'Statements.lean').read_text(encoding='utf-8')
hy = (SRC / 'Hypotheses.lean').read_text(encoding='utf-8')
assert st == (ORIG / 'Statements.lean').read_text(encoding='utf-8'), 'Statements.lean changed'
assert hashlib.sha256(st.encode()).hexdigest().startswith('ef3ebe7f')
st_head, st_imp, st_body = split(st)
hy_head, hy_imp, hy_body = split(hy)
imports = list(st_imp)
for l in hy_imp:
    if l.startswith('import Mathlib') and l not in imports:
        imports.append(l)
assert all(l.startswith('import Mathlib') for l in imports), imports

MARK_S0 = '-- BEGIN verbatim copy of UndecidablePhaseDiagram/Statements.lean (after its imports)'
MARK_S1 = '-- END verbatim copy of UndecidablePhaseDiagram/Statements.lean'
MARK_H0 = '-- BEGIN verbatim copy of UndecidablePhaseDiagram/Hypotheses.lean (after its imports)'
MARK_H1 = '-- END verbatim copy of UndecidablePhaseDiagram/Hypotheses.lean'

note = '''/-
# Challenge (comparator)

This file imports only Mathlib. It copies, byte for byte, the text of `Statements.lean` (the definitions
and the propositions `TheoremA`, `CorollaryB`, `ExistsUniversal`) and of `Hypotheses.lean` (the named
hypotheses `H1`, `H2` with their vocabulary) after their import blocks, between the BEGIN/END markers
below; nothing else defines a statement. `run_cmd ... setMainModule` before each copy only aligns
generated and private names with those of the development. `Statements.lean` is compiled in the
development with the Lean 4.35 compatibility option `backward.isDefEq.respectTransparency = false`
(Mathlib's `deriving Fintype` for enumeration types needs it at this pin), so its copy is elaborated with
the same option, which is reset to its default before the `Hypotheses.lean` copy. Within one file Lean
reuses an identical pattern-matching auxiliary ("matcher") made earlier in that file, while the separate
module `Hypotheses.lean` starts with an empty matcher cache (so `Ising.val` there has its own
`Ising.val.match_1`, not the matcher of `deriving Repr` for `Spin`). The matcher cache is keyed by
`bootstrap.genMatcherCode`, so setting it to `false` for the `Hypotheses.lean` copy (which lies in a
`noncomputable section`; only code generation for its matchers is skipped) reproduces the fresh cache;
it is reset afterwards. The comparator checks every constant of the statements against the development.
The three holes at the end are the final theorems of `Main.lean`, with the same binders.
-/'''

holes = '''namespace UPD

theorem theorem_A (h1 : H1) (h2 : H2) : TheoremA := by sorry

theorem corollary_B (h1 : H1) (h2 : H2) : CorollaryB := by sorry

theorem existsUniversal : ExistsUniversal := by sorry

end UPD
'''

parts = [
    st_head,
    '\n'.join(imports),
    '',
    note,
    '',
    'set_option backward.isDefEq.respectTransparency false',
    '',
    'run_cmd Lean.modifyEnv (fun env => env.setMainModule `UndecidablePhaseDiagram.Statements)',
    '',
    MARK_S0,
    st_body.rstrip('\n'),
    MARK_S1,
    'end',
    '',
    'set_option backward.isDefEq.respectTransparency true',
    '',
    'set_option bootstrap.genMatcherCode false',
    '',
    MARK_H0,
    hy_head.rstrip('\n'),
    '',
    'run_cmd Lean.modifyEnv (fun env => env.setMainModule `UndecidablePhaseDiagram.Hypotheses)',
    '',
    hy_body.rstrip('\n'),
    MARK_H1,
    'end',
    '',
    'set_option bootstrap.genMatcherCode true',
    '',
    'run_cmd Lean.modifyEnv (fun env => env.setMainModule `Challenge)',
    '',
    holes,
]
out = '\n'.join(parts)
# --- self-check: re-extract the copies
o = out.split('\n')
def between(a, b):
    return '\n'.join(o[o.index(a) + 1:o.index(b)])
s_copy = between(MARK_S0, MARK_S1)
assert s_copy == st_body.rstrip('\n'), 'Statements copy differs'
h_block = between(MARK_H0, MARK_H1)
assert h_block.startswith(hy_head.rstrip('\n')) and h_block.endswith(hy_body.rstrip('\n'))
assert out.count('sorry') == 3 and holes.count('sorry') == 3
for bad in ['native_decide', 'implemented_by', '@[extern', 'decide +native']:
    assert bad not in out, bad
assert not re.search(r'^\s*axiom\s', out, re.M)
(D / 'project' / 'Challenge.lean').write_text(out, encoding='utf-8', newline='\n')
rec = {
    'challenge_sha256': hashlib.sha256(out.encode()).hexdigest(),
    'challenge_imports': [l.split()[1] for l in imports],
    'challenge_imports_only_mathlib': True,
    'statements_file_sha256': hashlib.sha256(st.encode()).hexdigest(),
    'statements_file_original_sha256': hashlib.sha256((ORIG / 'Statements.lean').read_bytes()).hexdigest(),
    'hypotheses_file_sha256': hashlib.sha256(hy.encode()).hexdigest(),
    'hypotheses_file_original_sha256': hashlib.sha256((ORIG / 'Hypotheses.lean').read_bytes()).hexdigest(),
    'statements_copy_after_imports_sha256': hashlib.sha256(s_copy.encode()).hexdigest(),
    'statements_copy_byte_identical_to_source_after_imports': True,
    'hypotheses_copy_after_imports_sha256': hashlib.sha256(hy_body.rstrip('\n').encode()).hexdigest(),
    'hypotheses_copy_byte_identical_to_source_after_imports': True,
    'statements_lean_utf8': st,
    'hypotheses_lean_utf8': hy,
    'targets': [
        {'name': 'UPD.theorem_A', 'statement_utf8': 'theorem theorem_A (h1 : H1) (h2 : H2) : TheoremA', 'source': 'Main.lean (namespace UPD)'},
        {'name': 'UPD.corollary_B', 'statement_utf8': 'theorem corollary_B (h1 : H1) (h2 : H2) : CorollaryB', 'source': 'Main.lean (namespace UPD)'},
        {'name': 'UPD.existsUniversal', 'statement_utf8': 'theorem existsUniversal : ExistsUniversal', 'source': 'Main.lean (namespace UPD)'},
    ],
    'compatibility_option': 'backward.isDefEq.respectTransparency = false for the Statements copy (set_option before it, reset to true after it); the development compiles Statements.lean unchanged with -Dbackward.isDefEq.respectTransparency=false.',
    'matcher_cache_option': 'bootstrap.genMatcherCode = false for the Hypotheses copy only (reset to true after it): Lean reuses identical matchers within one file, so without it UPD.Ising.val would reuse UPD.instReprSpin.repr.match_1 from the Statements copy instead of its own UPD.Ising.val.match_1 as in the separate module Hypotheses.lean (first comparator run: "Const does not match between challenge and target UPD.Ising.val").',
    'independence': 'Only Mathlib imports; byte-identical copies of Statements.lean and Hypotheses.lean after their imports; no type_of%; generated/private names aligned by selecting the original module (setMainModule) while elaborating each copy.',
}
for t in rec['targets']:
    t['sha256'] = hashlib.sha256(t['statement_utf8'].encode()).hexdigest()
(D / 'evidence').mkdir(exist_ok=True)
(D / 'evidence' / 'FROZEN-STATEMENT.json').write_text(json.dumps(rec, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print('Challenge.lean', len(out), 'bytes, sha256', rec['challenge_sha256'])
print('imports', rec['challenge_imports'])
