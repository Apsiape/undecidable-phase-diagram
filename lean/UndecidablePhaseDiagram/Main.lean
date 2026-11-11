/-
# The final theorems: Theorem A and Corollary B

`Statements.lean` states Theorem A and Corollary B as the propositions `TheoremA` and
`CorollaryB` (the pattern QB ruled for the forgetting core). The proofs:
* the properties of `Φ` (`Interaction/Basic.lean`) and of the windows `J_n`
  (`Proof/Windows.lean`) are proved;
* the dichotomy and the "Moreover" clause of `thm:main` are in `Proof/MainTheorem.lean` (open);
* Corollary B follows from the dichotomy (`Proof/CorollaryB.lean`, proved).

The named hypotheses `H1` (Dobrushin's uniqueness theorem) and `H2` (the plus state of the
two-dimensional Ising model), signed off by QB in session 2 and stated in `Hypotheses.lean`, are
explicit arguments; `#print axioms` stays clean.
-/
import UndecidablePhaseDiagram.Interaction.Basic
import UndecidablePhaseDiagram.Proof.Windows
import UndecidablePhaseDiagram.Proof.CorollaryB
import UndecidablePhaseDiagram.Proof.MainTheorem

set_option autoImplicit false

namespace UPD

/-- **Theorem A** (`thm:main`, `prf:windows` and the properties of `Φ`). -/
theorem theorem_A (h1 : H1) (h2 : H2) : TheoremA := fun U =>
  ⟨phi_isInteraction, phi_translationInvariant, phi_nearestNeighbour, phi_values,
    fun _ hn => betaN_sub_pos hn, fun _ _ _ h => J_disjoint h,
    fun _ hn _ hβ => ⟨thm_main_i h1 U hn hβ, thm_main_ii h1 h2 U hn hβ⟩,
    fun _ hβ => thm_main_moreover U hβ⟩

/-- **Corollary B** (`cor:undecidable`). -/
theorem corollary_B (h1 : H1) (h2 : H2) : CorollaryB := fun U hU =>
  corollaryB_of_main U hU fun _ hn _ hβ => ⟨thm_main_i h1 U hn hβ, thm_main_ii h1 h2 U hn hβ⟩

/-- Non-vacuity of Corollary B: a universal machine exists. -/
theorem existsUniversal : ExistsUniversal := exists_universal

end UPD
