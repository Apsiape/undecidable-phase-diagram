"""Generate the package's root Audit.lean (run in WSL with python3 -I -B).

Model: /opt/forgetting-arxiv-2026-11-10/project/Audit.lean. It imports the root module (the whole
development, including UndecidablePhaseDiagram.Audit), prints and strictly audits every root of the
development's audit file (the three final theorems first), then audits the axioms of every imported
project declaration, including private and generated ones, and checks the types of the three final
theorems against their statements.
"""
from pathlib import Path
import re

D = Path('/opt/undecidable-phase-diagram-arxiv-2026-11-11')
P = D / 'project'
src = (P / 'UndecidablePhaseDiagram' / 'Audit.lean').read_text(encoding='utf-8')
roots = []
for m in re.finditer(r'^#audit_axioms(?:_strict)?\s+(\S+)\s*$', src, re.M):
    if m.group(1) not in roots:
        roots.append(m.group(1))
final = ['UPD.theorem_A', 'UPD.corollary_B', 'UPD.existsUniversal']
for f in final:
    assert f in roots, f
ordered = final + [r for r in roots if r not in final]
lines = [
    '/-',
    '# Complete axiom audit (release package, Lean v4.35.0, Mathlib 56a0058)',
    '',
    'Prints and strictly audits every root of `UndecidablePhaseDiagram/Audit.lean` (the three final',
    'theorems first), then checks the axioms of every imported declaration of the development, including',
    'private and generated ones: only `propext`, `Classical.choice`, `Quot.sound` are allowed, and no project',
    'declaration is an axiom. Finally it checks the types of the three final theorems.',
    '(Modelled on the forgetting relay, /opt/forgetting-arxiv-2026-11-10/project/Audit.lean.)',
    '-/',
    'import UndecidablePhaseDiagram',
    '',
    'set_option autoImplicit false',
    '',
]
for r in ordered:
    lines.append(f'#print axioms {r}')
    lines.append(f'#audit_axioms_strict {r}')
lines += [
    '',
    '/-! Complete imported-project audit, including generated and private declarations. -/',
    'set_option maxHeartbeats 20000000',
    'open Lean Elab Command',
    'run_cmd do',
    '  let env ← getEnv',
    '  let standard := [``propext, ``Classical.choice, ``Quot.sound]',
    '  let mut count := 0',
    '  for (n, ci) in env.constants.toList do',
    '    if let some idx := env.getModuleIdxFor? n then',
    '      let mod := env.allImportedModuleNames[idx]!',
    '      if mod.toString.startsWith "UndecidablePhaseDiagram" then',
    '        if ci matches .axiomInfo _ then throwError "Project axiom declaration {n}"',
    '        let ax := (← Lean.collectAxioms n).toList',
    '        for a in ax do',
    '          unless standard.contains a do throwError "Unexpected axiom {a} in {n}"',
    '        logInfo m!"UPD_DECL:{toJson (n.toString, mod.toString, ax.map Name.toString) |>.compress}"',
    '        count := count + 1',
    '  let check (n : Name) (t : Expr) : CommandElabM Unit := do',
    '    let some ci := env.find? n | throwError "Missing {n}"',
    '    unless ci matches .thmInfo _ do throwError "{n} is not a theorem"',
    '    unless ci.type == t do throwError "{n} statement changed"',
    '  check ``UPD.theorem_A (mkForall `h1 .default (mkConst ``UPD.H1)',
    '    (mkForall `h2 .default (mkConst ``UPD.H2) (mkConst ``UPD.TheoremA)))',
    '  check ``UPD.corollary_B (mkForall `h1 .default (mkConst ``UPD.H1)',
    '    (mkForall `h2 .default (mkConst ``UPD.H2) (mkConst ``UPD.CorollaryB)))',
    '  check ``UPD.existsUniversal (mkConst ``UPD.ExistsUniversal)',
    '  logInfo m!"UPD_FINAL_TYPES_OK"',
    '  logInfo m!"UPD_DECL_COUNT:{count}"',
    '',
]
(P / 'Audit.lean').write_text('\n'.join(lines), encoding='utf-8', newline='\n')
print('roots', len(ordered))
