/-
# The axiom-audit command

`#audit_axioms c` collects the axioms that the constant `c` depends on.
* `propext`, `Classical.choice`, `Quot.sound` are allowed.
* `sorryAx` is reported as a warning while the formalization is in progress
  (it marks an unfinished proof, and `STATUS.md` keeps the census).
* Every other axiom (for example `Lean.ofReduceBool` from `native_decide`, or a stray `axiom`
  declaration) is an error, so the audit file fails to compile.

`#audit_axioms_strict c` treats `sorryAx` as an error too; finished leaves are audited strictly.
(Copied from the forgetting project, `FixedNoiseErgodicity/AuditCommand.lean`.)
-/
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace UPD.Audit

/-- The axioms allowed in the finished core. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Shared implementation of the two audit commands. -/
def runAudit (id : Syntax) (strict : Bool) : CommandElabM Unit := do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter fun a => !(allowedAxioms.contains a) && a != ``sorryAx
  let hasSorry := axs.contains ``sorryAx
  logInfo m!"{n} depends on axioms: {axs.toList}"
  unless bad.isEmpty do
    logError m!"{n} depends on disallowed axioms: {bad.toList}"
  if hasSorry then
    if strict then logError m!"{n} depends on sorryAx"
    else logWarning m!"{n} depends on sorryAx (unfinished proof)"

/-- `#audit_axioms c`: allowed axioms only, `sorryAx` tolerated with a warning. -/
elab "#audit_axioms " id:ident : command => runAudit id false

/-- `#audit_axioms_strict c`: allowed axioms only, `sorryAx` is an error. -/
elab "#audit_axioms_strict " id:ident : command => runAudit id true

end UPD.Audit
