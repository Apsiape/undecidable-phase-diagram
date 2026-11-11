/-
# Complete axiom audit (release package, Lean v4.35.0, Mathlib 56a0058)

Prints and strictly audits every root of `UndecidablePhaseDiagram/Audit.lean` (the three final
theorems first), then checks the axioms of every imported declaration of the development, including
private and generated ones: only `propext`, `Classical.choice`, `Quot.sound` are allowed, and no project
declaration is an axiom. Finally it checks the types of the three final theorems.
(Modelled on the forgetting relay, /opt/forgetting-arxiv-2026-11-10/project/Audit.lean.)
-/
import UndecidablePhaseDiagram

set_option autoImplicit false

#print axioms UPD.theorem_A
#audit_axioms_strict UPD.theorem_A
#print axioms UPD.corollary_B
#audit_axioms_strict UPD.corollary_B
#print axioms UPD.existsUniversal
#audit_axioms_strict UPD.existsUniversal
#print axioms UPD.exists_universal
#audit_axioms_strict UPD.exists_universal
#print axioms UPD.thm_main_i
#audit_axioms_strict UPD.thm_main_i
#print axioms UPD.thm_main_ii
#audit_axioms_strict UPD.thm_main_ii
#print axioms UPD.thm_main_moreover
#audit_axioms_strict UPD.thm_main_moreover
#print axioms UPD.zfHyp
#audit_axioms_strict UPD.zfHyp
#print axioms UPD.Phi_singleton
#audit_axioms_strict UPD.Phi_singleton
#print axioms UPD.Phi_pairH
#audit_axioms_strict UPD.Phi_pairH
#print axioms UPD.Phi_pairV
#audit_axioms_strict UPD.Phi_pairV
#print axioms UPD.Phi_other
#audit_axioms_strict UPD.Phi_other
#print axioms UPD.phi_isInteraction
#audit_axioms_strict UPD.phi_isInteraction
#print axioms UPD.phi_translationInvariant
#audit_axioms_strict UPD.phi_translationInvariant
#print axioms UPD.phi_nearestNeighbour
#audit_axioms_strict UPD.phi_nearestNeighbour
#print axioms UPD.phi_values
#audit_axioms_strict UPD.phi_values
#print axioms UPD.windows_a
#audit_axioms_strict UPD.windows_a
#print axioms UPD.windows_b
#audit_axioms_strict UPD.windows_b
#print axioms UPD.windows_c
#audit_axioms_strict UPD.windows_c
#print axioms UPD.windows_c'
#audit_axioms_strict UPD.windows_c'
#print axioms UPD.windows_d
#audit_axioms_strict UPD.windows_d
#print axioms UPD.betaN_sub_pos
#audit_axioms_strict UPD.betaN_sub_pos
#print axioms UPD.J_disjoint
#audit_axioms_strict UPD.J_disjoint
#print axioms UPD.betaN_mem_J
#audit_axioms_strict UPD.betaN_mem_J
#print axioms UPD.bc_eq
#audit_axioms_strict UPD.bc_eq
#print axioms UPD.tanh_Jc
#audit_axioms_strict UPD.tanh_Jc
#print axioms UPD.thermal_a
#audit_axioms_strict UPD.thermal_a
#print axioms UPD.thermal_b
#audit_axioms_strict UPD.thermal_b
#print axioms UPD.thermal_c
#audit_axioms_strict UPD.thermal_c
#print axioms UPD.betaPair_spec
#audit_axioms_strict UPD.betaPair_spec
#print axioms UPD.primrec_betaPair
#audit_axioms_strict UPD.primrec_betaPair
#print axioms UPD.betaN_mem_unique_iff
#audit_axioms_strict UPD.betaN_mem_unique_iff
#print axioms UPD.corollaryB_of_main
#audit_axioms_strict UPD.corollaryB_of_main
#print axioms UPD.Scaffold.Formal.baseList_length
#audit_axioms_strict UPD.Scaffold.Formal.baseList_length
#print axioms UPD.Scaffold.Letter.letters_length
#audit_axioms_strict UPD.Scaffold.Letter.letters_length
#print axioms UPD.Scaffold.card_letterA
#audit_axioms_strict UPD.Scaffold.card_letterA
#print axioms UPD.Scaffold.card_quarter
#audit_axioms_strict UPD.Scaffold.card_quarter
#print axioms UPD.Scaffold.Thick.vRed_unique
#audit_axioms_strict UPD.Scaffold.Thick.vRed_unique
#print axioms UPD.Scaffold.Thick.hRed_unique
#audit_axioms_strict UPD.Scaffold.Thick.hRed_unique
#print axioms UPD.fill_agrees
#audit_axioms_strict UPD.fill_agrees
#print axioms UPD.fill_restrict
#audit_axioms_strict UPD.fill_restrict
#print axioms UPD.fill_injective
#audit_axioms_strict UPD.fill_injective
#print axioms UPD.walker_halts
#audit_axioms_strict UPD.walker_halts
#print axioms UPD.leftFirst_not_halts
#audit_axioms_strict UPD.leftFirst_not_halts
#print axioms UPD.deltaM_acc
#audit_axioms_strict UPD.deltaM_acc
#print axioms UPD.deltaM_fail
#audit_axioms_strict UPD.deltaM_fail
#print axioms UPD.initM_start
#audit_axioms_strict UPD.initM_start
#print axioms UPD.Gibbs.sum_fillOn_fillOn
#audit_axioms_strict UPD.Gibbs.sum_fillOn_fillOn
#print axioms UPD.Gibbs.mem_iff_of_cylinderEvents
#audit_axioms_strict UPD.Gibbs.mem_iff_of_cylinderEvents
#print axioms UPD.Gibbs.WeightSystem.expect_expect
#audit_axioms_strict UPD.Gibbs.WeightSystem.expect_expect
#print axioms UPD.Gibbs.WeightSystem.toSpecification
#audit_axioms_strict UPD.Gibbs.WeightSystem.toSpecification
#print axioms UPD.Gibbs.WeightSystem.isQuasilocal
#audit_axioms_strict UPD.Gibbs.WeightSystem.isQuasilocal
#print axioms UPD.Gibbs.WeightSystem.isGibbsMeasure_of_isDLR
#audit_axioms_strict UPD.Gibbs.WeightSystem.isGibbsMeasure_of_isDLR
#print axioms UPD.Gibbs.abs_logistic_sub_le
#audit_axioms_strict UPD.Gibbs.abs_logistic_sub_le
#print axioms UPD.Gibbs.IsingGraph.toWeightSystem
#audit_axioms_strict UPD.Gibbs.IsingGraph.toWeightSystem
#print axioms UPD.Gibbs.IsingGraph.dobrushinCoeff_le
#audit_axioms_strict UPD.Gibbs.IsingGraph.dobrushinCoeff_le
#print axioms UPD.Gibbs.IsingGraph.dobrushinConstant_lt_one
#audit_axioms_strict UPD.Gibbs.IsingGraph.dobrushinConstant_lt_one
#print axioms UPD.Gibbs.IsingGraph.dobrushin_unique
#audit_axioms_strict UPD.Gibbs.IsingGraph.dobrushin_unique
#print axioms UPD.Gibbs.measurableSet_legal
#audit_axioms_strict UPD.Gibbs.measurableSet_legal
#print axioms UPD.Gibbs.energy_lt_top_of_legal
#audit_axioms_strict UPD.Gibbs.energy_lt_top_of_legal
#print axioms UPD.Gibbs.partitionFunction_pos
#audit_axioms_strict UPD.Gibbs.partitionFunction_pos
#print axioms UPD.Gibbs.kernelApply_eq_integral
#audit_axioms_strict UPD.Gibbs.kernelApply_eq_integral
#print axioms UPD.Gibbs.isProbability_gibbsKernel
#audit_axioms_strict UPD.Gibbs.isProbability_gibbsKernel
#print axioms UPD.Gibbs.measurable_kernelApply
#audit_axioms_strict UPD.Gibbs.measurable_kernelApply
#print axioms UPD.Gibbs.abs_kernelApply_le
#audit_axioms_strict UPD.Gibbs.abs_kernelApply_le
#print axioms UPD.Ising.mem_bonds
#audit_axioms_strict UPD.Ising.mem_bonds
#print axioms UPD.Peierls.par_eq
#audit_axioms_strict UPD.Peierls.par_eq
#print axioms UPD.Peierls.par_add_e2
#audit_axioms_strict UPD.Peierls.par_add_e2
#print axioms UPD.Peierls.par_add_bondDir
#audit_axioms_strict UPD.Peierls.par_add_bondDir
#print axioms UPD.Peierls.par_eq_zero_of_left
#audit_axioms_strict UPD.Peierls.par_eq_zero_of_left
#print axioms UPD.Peierls.disagree_isEven
#audit_axioms_strict UPD.Peierls.disagree_isEven
#print axioms UPD.Peierls.par_disagree
#audit_axioms_strict UPD.Peierls.par_disagree
#print axioms UPD.Peierls.disagree_flip
#audit_axioms_strict UPD.Peierls.disagree_flip
#print axioms UPD.Peierls.weight_eq
#audit_axioms_strict UPD.Peierls.weight_eq
#print axioms UPD.Peierls.disagree_flipInside
#audit_axioms_strict UPD.Peierls.disagree_flipInside
#print axioms UPD.Peierls.par_eq_zero_off_box
#audit_axioms_strict UPD.Peierls.par_eq_zero_off_box
#print axioms UPD.Peierls.plus_prob_contour_le
#audit_axioms_strict UPD.Peierls.plus_prob_contour_le
#print axioms UPD.Peierls.plaq_toFinset_walk
#audit_axioms_strict UPD.Peierls.plaq_toFinset_walk
#print axioms UPD.Peierls.exists_closed_extension
#audit_axioms_strict UPD.Peierls.exists_closed_extension
#print axioms UPD.Peierls.exists_circuit_subset
#audit_axioms_strict UPD.Peierls.exists_circuit_subset
#print axioms UPD.Peierls.exists_circuit_par
#audit_axioms_strict UPD.Peierls.exists_circuit_par
#print axioms UPD.Peierls.exists_left_crossing
#audit_axioms_strict UPD.Peierls.exists_left_crossing
#print axioms UPD.Peierls.circuit_code
#audit_axioms_strict UPD.Peierls.circuit_code
#print axioms UPD.Peierls.card_contours_le
#audit_axioms_strict UPD.Peierls.card_contours_le
#print axioms UPD.Peierls.hasSum_series
#audit_axioms_strict UPD.Peierls.hasSum_series
#print axioms UPD.Peierls.sum_contours_le
#audit_axioms_strict UPD.Peierls.sum_contours_le
#print axioms UPD.Peierls.plus_prob_minus_le
#audit_axioms_strict UPD.Peierls.plus_prob_minus_le
#print axioms UPD.Peierls.expect_flip
#audit_axioms_strict UPD.Peierls.expect_flip
#print axioms UPD.Peierls.IsIsingGibbs.map_flip
#audit_axioms_strict UPD.Peierls.IsIsingGibbs.map_flip
#print axioms UPD.Peierls.IsLimitState.map_flip
#audit_axioms_strict UPD.Peierls.IsLimitState.map_flip
#print axioms UPD.Peierls.isTranslationInvariant_map_flip
#audit_axioms_strict UPD.Peierls.isTranslationInvariant_map_flip
#print axioms UPD.Peierls.plus_state_bound
#audit_axioms_strict UPD.Peierls.plus_state_bound
#print axioms UPD.Peierls.peierls
#audit_axioms_strict UPD.Peierls.peierls
#print axioms UPD.Gibbs.WeightSystem.integral_kernel
#audit_axioms_strict UPD.Gibbs.WeightSystem.integral_kernel
#print axioms UPD.Gibbs.WeightSystem.isDLR_of_isGibbsMeasure
#audit_axioms_strict UPD.Gibbs.WeightSystem.isDLR_of_isGibbsMeasure
#print axioms UPD.Gibbs.WeightSystem.exists_isDLR
#audit_axioms_strict UPD.Gibbs.WeightSystem.exists_isDLR
#print axioms UPD.Gibbs.IsingGraph.exists_isDLR
#audit_axioms_strict UPD.Gibbs.IsingGraph.exists_isDLR
#print axioms UPD.Gibbs.IsingGraph.existsUnique_isDLR
#audit_axioms_strict UPD.Gibbs.IsingGraph.existsUnique_isDLR
#print axioms UPD.Peierls.bondEdge_injective
#audit_axioms_strict UPD.Peierls.bondEdge_injective
#print axioms UPD.Peierls.edgesMeeting_eq
#audit_axioms_strict UPD.Peierls.edgesMeeting_eq
#print axioms UPD.Peierls.weight_squareLattice
#audit_axioms_strict UPD.Peierls.weight_squareLattice
#print axioms UPD.Peierls.expect_squareLattice
#audit_axioms_strict UPD.Peierls.expect_squareLattice
#print axioms UPD.Peierls.isIsingGibbs_iff
#audit_axioms_strict UPD.Peierls.isIsingGibbs_iff
#print axioms UPD.Peierls.peierls_squareLattice
#audit_axioms_strict UPD.Peierls.peierls_squareLattice
#print axioms UPD.Gibbs.HardWeightSystem.expect_expect
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.expect_expect
#print axioms UPD.Gibbs.HardWeightSystem.abs_expect_le
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.abs_expect_le
#print axioms UPD.Gibbs.HardWeightSystem.measurable_expect
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.measurable_expect
#print axioms UPD.Gibbs.HardWeightSystem.dlr_of_superset
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.dlr_of_superset
#print axioms UPD.Gibbs.boltzmann_add
#audit_axioms_strict UPD.Gibbs.boltzmann_add
#print axioms UPD.Gibbs.energy_add
#audit_axioms_strict UPD.Gibbs.energy_add
#print axioms UPD.Gibbs.siteSystem
#audit_axioms_strict UPD.Gibbs.siteSystem
#print axioms UPD.Gibbs.kernelApply_eq
#audit_axioms_strict UPD.Gibbs.kernelApply_eq
#print axioms UPD.Gibbs.isLegal_iff
#audit_axioms_strict UPD.Gibbs.isLegal_iff
#print axioms UPD.Gibbs.isGibbs_iff
#audit_axioms_strict UPD.Gibbs.isGibbs_iff
#print axioms UPD.MachineM.nextRow_stay
#audit_axioms_strict UPD.MachineM.nextRow_stay
#print axioms UPD.MachineM.nextRow_up
#audit_axioms_strict UPD.MachineM.nextRow_up
#print axioms UPD.MachineM.nextRow_down
#audit_axioms_strict UPD.MachineM.nextRow_down
#print axioms UPD.MachineM.nextRow_up_fail
#audit_axioms_strict UPD.MachineM.nextRow_up_fail
#print axioms UPD.MachineM.nextRow_down_fail
#audit_axioms_strict UPD.MachineM.nextRow_down_fail
#print axioms UPD.Scaffold.Formal.inO_child
#audit_axioms_strict UPD.Scaffold.Formal.inO_child
#print axioms UPD.Scaffold.Formal.legalOn_phi_iff
#audit_axioms_strict UPD.Scaffold.Formal.legalOn_phi_iff
#print axioms UPD.Scaffold.Formal.child_injective
#audit_axioms_strict UPD.Scaffold.Formal.child_injective
#print axioms UPD.Scaffold.Letter.InA.child
#audit_axioms_strict UPD.Scaffold.Letter.InA.child
#print axioms UPD.Scaffold.Letter.legalOn_phi'_iff
#audit_axioms_strict UPD.Scaffold.Letter.legalOn_phi'_iff
#print axioms UPD.Scaffold.Letter.child_injective
#audit_axioms_strict UPD.Scaffold.Letter.child_injective
#print axioms UPD.Scaffold.sigmaPow_legal
#audit_axioms_strict UPD.Scaffold.sigmaPow_legal
#print axioms UPD.Scaffold.exists_letter_tiling
#audit_axioms_strict UPD.Scaffold.exists_letter_tiling
#print axioms UPD.Scaffold.exists_tower
#audit_axioms_strict UPD.Scaffold.exists_tower
#print axioms UPD.Scaffold.eq_digits
#audit_axioms_strict UPD.Scaffold.eq_digits
#print axioms UPD.Scaffold.emod_eq_wsum_dig
#audit_axioms_strict UPD.Scaffold.emod_eq_wsum_dig
#print axioms UPD.Scaffold.rank_bits_col
#audit_axioms_strict UPD.Scaffold.rank_bits_col
#print axioms UPD.Scaffold.rank_bits_row
#audit_axioms_strict UPD.Scaffold.rank_bits_row
#print axioms UPD.Scaffold.red_col
#audit_axioms_strict UPD.Scaffold.red_col
#print axioms UPD.Scaffold.red_row
#audit_axioms_strict UPD.Scaffold.red_row
#print axioms UPD.Scaffold.Quarter.matchE_iff
#audit_axioms_strict UPD.Scaffold.Quarter.matchE_iff
#print axioms UPD.Scaffold.Quarter.matchN_iff
#audit_axioms_strict UPD.Scaffold.Quarter.matchN_iff
#print axioms UPD.Scaffold.legalOn_quartering_iff
#audit_axioms_strict UPD.Scaffold.legalOn_quartering_iff
#print axioms UPD.Scaffold.VW_eq
#audit_axioms_strict UPD.Scaffold.VW_eq
#print axioms UPD.Scaffold.HW_eq
#audit_axioms_strict UPD.Scaffold.HW_eq
#print axioms UPD.Scaffold.walls_col
#audit_axioms_strict UPD.Scaffold.walls_col
#print axioms UPD.Scaffold.walls_row
#audit_axioms_strict UPD.Scaffold.walls_row
#print axioms UPD.Scaffold.frameOffsets_phase
#audit_axioms_strict UPD.Scaffold.frameOffsets_phase
#print axioms UPD.Scaffold.frame_window_unique
#audit_axioms_strict UPD.Scaffold.frame_window_unique
#print axioms UPD.Scaffold.endpoint_not_inFrame
#audit_axioms_strict UPD.Scaffold.endpoint_not_inFrame
#print axioms UPD.Scaffold.frames_nested
#audit_axioms_strict UPD.Scaffold.frames_nested
#print axioms UPD.Scaffold.frames_contain
#audit_axioms_strict UPD.Scaffold.frames_contain
#print axioms UPD.Scaffold.isFree_rfree
#audit_axioms_strict UPD.Scaffold.isFree_rfree
#print axioms UPD.Scaffold.isFree_frameHi_sub_one
#audit_axioms_strict UPD.Scaffold.isFree_frameHi_sub_one
#print axioms UPD.Scaffold.rfree_emod
#audit_axioms_strict UPD.Scaffold.rfree_emod
#print axioms UPD.Scaffold.rfree_emod_of_lt
#audit_axioms_strict UPD.Scaffold.rfree_emod_of_lt
#print axioms UPD.Scaffold.rfree_depth_unique
#audit_axioms_strict UPD.Scaffold.rfree_depth_unique
#print axioms UPD.Scaffold.interior_of_digit_two
#audit_axioms_strict UPD.Scaffold.interior_of_digit_two
#print axioms UPD.Scaffold.Laminar.endpoint_unique
#audit_axioms_strict UPD.Scaffold.Laminar.endpoint_unique
#print axioms UPD.Scaffold.Laminar.mem_of_consecutive
#audit_axioms_strict UPD.Scaffold.Laminar.mem_of_consecutive
#print axioms UPD.Scaffold.Laminar.consecutive_of_minimal
#audit_axioms_strict UPD.Scaffold.Laminar.consecutive_of_minimal
#print axioms UPD.Scaffold.own_spec
#audit_axioms_strict UPD.Scaffold.own_spec
#print axioms UPD.Scaffold.thin_phase
#audit_axioms_strict UPD.Scaffold.thin_phase
#print axioms UPD.Scaffold.thin_phase_unique
#audit_axioms_strict UPD.Scaffold.thin_phase_unique
#print axioms UPD.Scaffold.parents_eq
#audit_axioms_strict UPD.Scaffold.parents_eq
#print axioms UPD.Scaffold.parents_check
#audit_axioms_strict UPD.Scaffold.parents_check
#print axioms UPD.Scaffold.parent_inO
#audit_axioms_strict UPD.Scaffold.parent_inO
#print axioms UPD.Scaffold.base_desub
#audit_axioms_strict UPD.Scaffold.base_desub
#print axioms UPD.Scaffold.witness_col
#audit_axioms_strict UPD.Scaffold.witness_col
#print axioms UPD.Scaffold.witness_row
#audit_axioms_strict UPD.Scaffold.witness_row
#print axioms UPD.Scaffold.desub
#audit_axioms_strict UPD.Scaffold.desub
#print axioms UPD.Scaffold.exists_tower_of_tiling
#audit_axioms_strict UPD.Scaffold.exists_tower_of_tiling
#print axioms UPD.Scaffold.tower_unique
#audit_axioms_strict UPD.Scaffold.tower_unique
#print axioms UPD.Scaffold.phase_shift
#audit_axioms_strict UPD.Scaffold.phase_shift
#print axioms UPD.Scaffold.phase_local
#audit_axioms_strict UPD.Scaffold.phase_local
#print axioms UPD.Scaffold.exists_phase
#audit_axioms_strict UPD.Scaffold.exists_phase
#print axioms UPD.Scaffold.coincidence
#audit_axioms_strict UPD.Scaffold.coincidence
#print axioms UPD.Scaffold.scaffold_ti_a
#audit_axioms_strict UPD.Scaffold.scaffold_ti_a
#print axioms UPD.Scaffold.scaffold_rigid
#audit_axioms_strict UPD.Scaffold.scaffold_rigid
#print axioms UPD.Scaffold.quarter_exists
#audit_axioms_strict UPD.Scaffold.quarter_exists
#print axioms UPD.Scaffold.quarter_unique
#audit_axioms_strict UPD.Scaffold.quarter_unique
#print axioms UPD.Scaffold.isQTiling_qshift
#audit_axioms_strict UPD.Scaffold.isQTiling_qshift
#print axioms UPD.Scaffold.IsQPhase.unique
#audit_axioms_strict UPD.Scaffold.IsQPhase.unique
#print axioms UPD.Scaffold.qphase_shift
#audit_axioms_strict UPD.Scaffold.qphase_shift
#print axioms UPD.Scaffold.qphase_local
#audit_axioms_strict UPD.Scaffold.qphase_local
#print axioms UPD.Scaffold.quarter_ti_a
#audit_axioms_strict UPD.Scaffold.quarter_ti_a
#print axioms UPD.Scaffold.quarter_rigid
#audit_axioms_strict UPD.Scaffold.quarter_rigid
#print axioms UPD.Scaffold.walls_VW
#audit_axioms_strict UPD.Scaffold.walls_VW
#print axioms UPD.Scaffold.walls_HW
#audit_axioms_strict UPD.Scaffold.walls_HW
#print axioms UPD.Scaffold.allowed_block
#audit_axioms_strict UPD.Scaffold.allowed_block
#print axioms UPD.Scaffold.sum_allowed
#audit_axioms_strict UPD.Scaffold.sum_allowed
#print axioms UPD.Scaffold.isFree_iff_allowed
#audit_axioms_strict UPD.Scaffold.isFree_iff_allowed
#print axioms UPD.Scaffold.card_free
#audit_axioms_strict UPD.Scaffold.card_free
#print axioms UPD.Scaffold.digit2_iff
#audit_axioms_strict UPD.Scaffold.digit2_iff
#print axioms UPD.Scaffold.Typical.inFrame_col
#audit_axioms_strict UPD.Scaffold.Typical.inFrame_col
#print axioms UPD.Scaffold.Typical.inFrame_row
#audit_axioms_strict UPD.Scaffold.Typical.inFrame_row
#print axioms UPD.Scaffold.unifSeq_cyl
#audit_axioms_strict UPD.Scaffold.unifSeq_cyl
#print axioms UPD.Scaffold.pi_eq_generateFrom_cyl
#audit_axioms_strict UPD.Scaffold.pi_eq_generateFrom_cyl
#print axioms UPD.Scaffold.ext_cyl
#audit_axioms_strict UPD.Scaffold.ext_cyl
#print axioms UPD.Scaffold.eq_unifSeq
#audit_axioms_strict UPD.Scaffold.eq_unifSeq
#print axioms UPD.Scaffold.sum_cyl
#audit_axioms_strict UPD.Scaffold.sum_cyl
#print axioms UPD.Scaffold.cyl_eq_of_const
#audit_axioms_strict UPD.Scaffold.cyl_eq_of_const
#print axioms UPD.Scaffold.unifSeq_map_tail
#audit_axioms_strict UPD.Scaffold.unifSeq_map_tail
#print axioms UPD.Scaffold.unifSeq_map_pairs
#audit_axioms_strict UPD.Scaffold.unifSeq_map_pairs
#print axioms UPD.Scaffold.unifSeq_forall_mem_null
#audit_axioms_strict UPD.Scaffold.unifSeq_forall_mem_null
#print axioms UPD.Scaffold.ae_exists_pair
#audit_axioms_strict UPD.Scaffold.ae_exists_pair
#print axioms UPD.Scaffold.dig_congr
#audit_axioms_strict UPD.Scaffold.dig_congr
#print axioms UPD.Scaffold.dig_dig
#audit_axioms_strict UPD.Scaffold.dig_dig
#print axioms UPD.Scaffold.digP_digP
#audit_axioms_strict UPD.Scaffold.digP_digP
#print axioms UPD.Scaffold.haar_map_digP
#audit_axioms_strict UPD.Scaffold.haar_map_digP
#print axioms UPD.Scaffold.haar_map_addDig
#audit_axioms_strict UPD.Scaffold.haar_map_addDig
#print axioms UPD.Scaffold.wsum_addDig
#audit_axioms_strict UPD.Scaffold.wsum_addDig
#print axioms UPD.Scaffold.ae_resolving
#audit_axioms_strict UPD.Scaffold.ae_resolving
#print axioms UPD.Scaffold.ae_typical
#audit_axioms_strict UPD.Scaffold.ae_typical
#print axioms UPD.Scaffold.measurableSet_legalOn_univ
#audit_axioms_strict UPD.Scaffold.measurableSet_legalOn_univ
#print axioms UPD.Scaffold.PhaseSystem.shift_Ψ
#audit_axioms_strict UPD.Scaffold.PhaseSystem.shift_Ψ
#print axioms UPD.Scaffold.PhaseSystem.isTILaw
#audit_axioms_strict UPD.Scaffold.PhaseSystem.isTILaw
#print axioms UPD.Scaffold.PhaseSystem.cyl_const
#audit_axioms_strict UPD.Scaffold.PhaseSystem.cyl_const
#print axioms UPD.Scaffold.PhaseSystem.law_phase
#audit_axioms_strict UPD.Scaffold.PhaseSystem.law_phase
#print axioms UPD.Scaffold.PhaseSystem.law_unique
#audit_axioms_strict UPD.Scaffold.PhaseSystem.law_unique
#print axioms UPD.Scaffold.PhaseSystem.existsUnique_isTILaw
#audit_axioms_strict UPD.Scaffold.PhaseSystem.existsUnique_isTILaw
#print axioms UPD.Scaffold.measurable_phaseOf
#audit_axioms_strict UPD.Scaffold.measurable_phaseOf
#print axioms UPD.Scaffold.tilingOf_eq
#audit_axioms_strict UPD.Scaffold.tilingOf_eq
#print axioms UPD.Scaffold.tilingOf_spec
#audit_axioms_strict UPD.Scaffold.tilingOf_spec
#print axioms UPD.Scaffold.measurable_tilingOf
#audit_axioms_strict UPD.Scaffold.measurable_tilingOf
#print axioms UPD.Scaffold.scaffold_ti_b
#audit_axioms_strict UPD.Scaffold.scaffold_ti_b
#print axioms UPD.Scaffold.scaffold_ti_existsUnique
#audit_axioms_strict UPD.Scaffold.scaffold_ti_existsUnique
#print axioms UPD.Scaffold.scaffold_phase_haar
#audit_axioms_strict UPD.Scaffold.scaffold_phase_haar
#print axioms UPD.Scaffold.measurable_qphaseOf
#audit_axioms_strict UPD.Scaffold.measurable_qphaseOf
#print axioms UPD.Scaffold.measurable_qtilingOf
#audit_axioms_strict UPD.Scaffold.measurable_qtilingOf
#print axioms UPD.Scaffold.qtilingOf_spec
#audit_axioms_strict UPD.Scaffold.qtilingOf_spec
#print axioms UPD.Scaffold.quarter_ti_law
#audit_axioms_strict UPD.Scaffold.quarter_ti_law
#print axioms UPD.Scaffold.quarter_ti_existsUnique
#audit_axioms_strict UPD.Scaffold.quarter_ti_existsUnique
#print axioms UPD.Scaffold.quarter_phase_haar
#audit_axioms_strict UPD.Scaffold.quarter_phase_haar
#print axioms UPD.Scaffold.quarter_phase_typical
#audit_axioms_strict UPD.Scaffold.quarter_phase_typical
#print axioms UPD.MachineM.nextRow_colOf
#audit_axioms_strict UPD.MachineM.nextRow_colOf
#print axioms UPD.MachineM.nextRow_iterate
#audit_axioms_strict UPD.MachineM.nextRow_iterate
#print axioms UPD.MachineM.runM_eq
#audit_axioms_strict UPD.MachineM.runM_eq
#print axioms UPD.MachineM.stepB_iterate
#audit_axioms_strict UPD.MachineM.stepB_iterate
#print axioms UPD.MachineM.stepU_iterate_fail
#audit_axioms_strict UPD.MachineM.stepU_iterate_fail
#print axioms UPD.MachineM.scan_up
#audit_axioms_strict UPD.MachineM.scan_up
#print axioms UPD.MachineM.scan_down
#audit_axioms_strict UPD.MachineM.scan_down
#print axioms UPD.MachineM.depth_loop
#audit_axioms_strict UPD.MachineM.depth_loop
#print axioms UPD.MachineM.depth_S1
#audit_axioms_strict UPD.MachineM.depth_S1
#print axioms UPD.MachineM.depth_fail
#audit_axioms_strict UPD.MachineM.depth_fail
#print axioms UPD.MachineM.depth_phase
#audit_axioms_strict UPD.MachineM.depth_phase
#print axioms UPD.MachineM.depth_fail_forever
#audit_axioms_strict UPD.MachineM.depth_fail_forever
#print axioms UPD.MachineM.ready_ge_eight
#audit_axioms_strict UPD.MachineM.ready_ge_eight
#print axioms UPD.MachineM.deltaM_H
#audit_axioms_strict UPD.MachineM.deltaM_H
#print axioms UPD.MachineM.pass_scan
#audit_axioms_strict UPD.MachineM.pass_scan
#print axioms UPD.MachineM.Reaches.trans
#audit_axioms_strict UPD.MachineM.Reaches.trans
#print axioms UPD.MachineM.scan_upX
#audit_axioms_strict UPD.MachineM.scan_upX
#print axioms UPD.MachineM.scan_downX
#audit_axioms_strict UPD.MachineM.scan_downX
#print axioms UPD.MachineM.iterate_head_le
#audit_axioms_strict UPD.MachineM.iterate_head_le
#print axioms UPD.MachineM.tapeL0_eq
#audit_axioms_strict UPD.MachineM.tapeL0_eq
#print axioms UPD.MachineM.div_add_pred
#audit_axioms_strict UPD.MachineM.div_add_pred
#print axioms UPD.MachineM.parK_tapeL
#audit_axioms_strict UPD.MachineM.parK_tapeL
#print axioms UPD.MachineM.dvd_pow_succ_iff
#audit_axioms_strict UPD.MachineM.dvd_pow_succ_iff
#print axioms UPD.MachineM.label_pass
#audit_axioms_strict UPD.MachineM.label_pass
#print axioms UPD.MachineM.label_even
#audit_axioms_strict UPD.MachineM.label_even
#print axioms UPD.MachineM.label_odd
#audit_axioms_strict UPD.MachineM.label_odd
#print axioms UPD.MachineM.label_iter
#audit_axioms_strict UPD.MachineM.label_iter
#print axioms UPD.MachineM.load
#audit_axioms_strict UPD.MachineM.load
#print axioms UPD.MachineM.sim_step
#audit_axioms_strict UPD.MachineM.sim_step
#print axioms UPD.MachineM.sim_step_none
#audit_axioms_strict UPD.MachineM.sim_step_none
#print axioms UPD.MachineM.sim_run
#audit_axioms_strict UPD.MachineM.sim_run
#print axioms UPD.MachineM.sim_not_halts
#audit_axioms_strict UPD.MachineM.sim_not_halts
#print axioms UPD.MachineM.sim_halts
#audit_axioms_strict UPD.MachineM.sim_halts
#print axioms UPD.MachineM.exists_firstHalt
#audit_axioms_strict UPD.MachineM.exists_firstHalt
#print axioms UPD.MachineM.sim_firstHalt
#audit_axioms_strict UPD.MachineM.sim_firstHalt
#print axioms UPD.MachineM.E0_return
#audit_axioms_strict UPD.MachineM.E0_return
#print axioms UPD.MachineM.mask_round
#audit_axioms_strict UPD.MachineM.mask_round
#print axioms UPD.MachineM.mask_rounds
#audit_axioms_strict UPD.MachineM.mask_rounds
#print axioms UPD.MachineM.mask_end1
#audit_axioms_strict UPD.MachineM.mask_end1
#print axioms UPD.MachineM.mask_end2
#audit_axioms_strict UPD.MachineM.mask_end2
#print axioms UPD.MachineM.mask_acc
#audit_axioms_strict UPD.MachineM.mask_acc
#print axioms UPD.MachineM.stepU_iterate_acc
#audit_axioms_strict UPD.MachineM.stepU_iterate_acc
#print axioms UPD.MachineM.run_acc
#audit_axioms_strict UPD.MachineM.run_acc
#print axioms UPD.MachineM.acc_after
#audit_axioms_strict UPD.MachineM.acc_after
#print axioms UPD.MachineM.stepB_eq_stepU_of_le
#audit_axioms_strict UPD.MachineM.stepB_eq_stepU_of_le
#print axioms UPD.MachineM.stepB_eq_of_head
#audit_axioms_strict UPD.MachineM.stepB_eq_of_head
#print axioms UPD.MachineM.colOf_zero_acc
#audit_axioms_strict UPD.MachineM.colOf_zero_acc
#print axioms UPD.MachineM.ready_a
#audit_axioms_strict UPD.MachineM.ready_a
#print axioms UPD.MachineM.lin_lt_two_pow
#audit_axioms_strict UPD.MachineM.lin_lt_two_pow
#print axioms UPD.MachineM.eventually_lin_lt
#audit_axioms_strict UPD.MachineM.eventually_lin_lt
#print axioms UPD.MachineM.timeL_le
#audit_axioms_strict UPD.MachineM.timeL_le
#print axioms UPD.MachineM.label_pow
#audit_axioms_strict UPD.MachineM.label_pow
#print axioms UPD.MachineM.ready_b
#audit_axioms_strict UPD.MachineM.ready_b
#print axioms UPD.MachineM.readyDepths_empty
#audit_axioms_strict UPD.MachineM.readyDepths_empty
#print axioms UPD.MachineM.readyDepths_infinite
#audit_axioms_strict UPD.MachineM.readyDepths_infinite
#print axioms UPD.Gibbs.WeightSystem.fillOn_comm
#audit_axioms_strict UPD.Gibbs.WeightSystem.fillOn_comm
#print axioms UPD.Gibbs.WeightSystem.fillOn_union
#audit_axioms_strict UPD.Gibbs.WeightSystem.fillOn_union
#print axioms UPD.Gibbs.WeightSystem.expect_union
#audit_axioms_strict UPD.Gibbs.WeightSystem.expect_union
#print axioms UPD.Gibbs.WeightSystem.expect_empty
#audit_axioms_strict UPD.Gibbs.WeightSystem.expect_empty
#print axioms UPD.Gibbs.WeightSystem.abs_expect_le'
#audit_axioms_strict UPD.Gibbs.WeightSystem.abs_expect_le'
#print axioms UPD.Gibbs.mem_lift
#audit_axioms_strict UPD.Gibbs.mem_lift
#print axioms UPD.Gibbs.fillOn_joinAt
#audit_axioms_strict UPD.Gibbs.fillOn_joinAt
#print axioms UPD.Gibbs.IsingGraph.edgesMeeting_lift
#audit_axioms_strict UPD.Gibbs.IsingGraph.edgesMeeting_lift
#print axioms UPD.Gibbs.IsingGraph.weight_lift
#audit_axioms_strict UPD.Gibbs.IsingGraph.weight_lift
#print axioms UPD.Gibbs.IsingGraph.expect_lift
#audit_axioms_strict UPD.Gibbs.IsingGraph.expect_lift
#print axioms UPD.Gibbs.joinAt_splitAt
#audit_axioms_strict UPD.Gibbs.joinAt_splitAt
#print axioms UPD.Gibbs.measurable_splitAt
#audit_axioms_strict UPD.Gibbs.measurable_splitAt
#print axioms UPD.Gibbs.measurable_joinAt
#audit_axioms_strict UPD.Gibbs.measurable_joinAt
#print axioms UPD.Gibbs.measurable_glue
#audit_axioms_strict UPD.Gibbs.measurable_glue
#print axioms UPD.Gibbs.map_splitAt_glue
#audit_axioms_strict UPD.Gibbs.map_splitAt_glue
#print axioms UPD.Gibbs.IsingGraph.weight_union_of_label
#audit_axioms_strict UPD.Gibbs.IsingGraph.weight_union_of_label
#print axioms UPD.Gibbs.IsingGraph.range_label
#audit_axioms_strict UPD.Gibbs.IsingGraph.range_label
#print axioms UPD.Gibbs.IsingGraph.expect_label
#audit_axioms_strict UPD.Gibbs.IsingGraph.expect_label
#print axioms UPD.Gibbs.IsingGraph.dlr_component
#audit_axioms_strict UPD.Gibbs.IsingGraph.dlr_component
#print axioms UPD.Gibbs.IsingGraph.isDLR_of_components
#audit_axioms_strict UPD.Gibbs.IsingGraph.isDLR_of_components
#print axioms UPD.Gibbs.IsingGraph.isDLR_glue
#audit_axioms_strict UPD.Gibbs.IsingGraph.isDLR_glue
#print axioms UPD.Gibbs.IsingGraph.Iso.fillOn_map
#audit_axioms_strict UPD.Gibbs.IsingGraph.Iso.fillOn_map
#print axioms UPD.Gibbs.IsingGraph.Iso.weight_map
#audit_axioms_strict UPD.Gibbs.IsingGraph.Iso.weight_map
#print axioms UPD.Gibbs.IsingGraph.Iso.expect_map
#audit_axioms_strict UPD.Gibbs.IsingGraph.Iso.expect_map
#print axioms UPD.Gibbs.IsingGraph.Iso.isDLR_map
#audit_axioms_strict UPD.Gibbs.IsingGraph.Iso.isDLR_map
#print axioms UPD.BG.chain
#audit_axioms_strict UPD.BG.chain
#print axioms UPD.BG.chain'
#audit_axioms_strict UPD.BG.chain'
#print axioms UPD.BG.Line.wall_iff
#audit_axioms_strict UPD.BG.Line.wall_iff
#print axioms UPD.BG.Line.wall_lo
#audit_axioms_strict UPD.BG.Line.wall_lo
#print axioms UPD.BG.Line.wall_hi
#audit_axioms_strict UPD.BG.Line.wall_hi
#print axioms UPD.BG.Line.interior_none
#audit_axioms_strict UPD.BG.Line.interior_none
#print axioms UPD.BG.Line.frameLo_lt
#audit_axioms_strict UPD.BG.Line.frameLo_lt
#print axioms UPD.BG.Line.lt_frameHi
#audit_axioms_strict UPD.BG.Line.lt_frameHi
#print axioms UPD.BG.Line.exists_wall_lt
#audit_axioms_strict UPD.BG.Line.exists_wall_lt
#print axioms UPD.BG.Line.exists_wall_gt
#audit_axioms_strict UPD.BG.Line.exists_wall_gt
#print axioms UPD.BG.Line.exists_nearest
#audit_axioms_strict UPD.BG.Line.exists_nearest
#print axioms UPD.BG.Line.o_const
#audit_axioms_strict UPD.BG.Line.o_const
#print axioms UPD.BG.Line.routing
#audit_axioms_strict UPD.BG.Line.routing
#print axioms UPD.BG.Line.carrier_iff
#audit_axioms_strict UPD.BG.Line.carrier_iff
#print axioms UPD.BG.Line.o_frame
#audit_axioms_strict UPD.BG.Line.o_frame
#print axioms UPD.BG.EvLine.first_wall
#audit_axioms_strict UPD.BG.EvLine.first_wall
#print axioms UPD.BG.EvLine.second_wall
#audit_axioms_strict UPD.BG.EvLine.second_wall
#print axioms UPD.BG.allowed_of_legal
#audit_axioms_strict UPD.BG.allowed_of_legal
#print axioms UPD.BG.matchH_of_legal
#audit_axioms_strict UPD.BG.matchH_of_legal
#print axioms UPD.BG.matchV_of_legal
#audit_axioms_strict UPD.BG.matchV_of_legal
#print axioms UPD.BG.Setting.VW_L
#audit_axioms_strict UPD.BG.Setting.VW_L
#print axioms UPD.BG.Setting.VW_R
#audit_axioms_strict UPD.BG.Setting.VW_R
#print axioms UPD.BG.Setting.HW_B
#audit_axioms_strict UPD.BG.Setting.HW_B
#print axioms UPD.BG.Setting.HW_T
#audit_axioms_strict UPD.BG.Setting.HW_T
#print axioms UPD.BG.Setting.routing_a
#audit_axioms_strict UPD.BG.Setting.routing_a
#print axioms UPD.BG.Setting.routing_a_v
#audit_axioms_strict UPD.BG.Setting.routing_a_v
#print axioms UPD.BG.Setting.exists_walls_h
#audit_axioms_strict UPD.BG.Setting.exists_walls_h
#print axioms UPD.BG.Setting.exists_walls_v
#audit_axioms_strict UPD.BG.Setting.exists_walls_v
#print axioms UPD.BG.Setting.routing_b_h
#audit_axioms_strict UPD.BG.Setting.routing_b_h
#print axioms UPD.BG.Setting.routing_b_v
#audit_axioms_strict UPD.BG.Setting.routing_b_v
#print axioms UPD.BG.own_eq_of_isFree
#audit_axioms_strict UPD.BG.own_eq_of_isFree
#print axioms UPD.BG.isFree_own
#audit_axioms_strict UPD.BG.isFree_own
#print axioms UPD.BG.Setting.routing_c
#audit_axioms_strict UPD.BG.Setting.routing_c
#print axioms UPD.BG.mem_freeSet
#audit_axioms_strict UPD.BG.mem_freeSet
#print axioms UPD.BG.card_freeSet
#audit_axioms_strict UPD.BG.card_freeSet
#print axioms UPD.BG.zeta_free
#audit_axioms_strict UPD.BG.zeta_free
#print axioms UPD.BG.zeta_lt_iff
#audit_axioms_strict UPD.BG.zeta_lt_iff
#print axioms UPD.BG.zeta_inj
#audit_axioms_strict UPD.BG.zeta_inj
#print axioms UPD.BG.exists_zeta
#audit_axioms_strict UPD.BG.exists_zeta
#print axioms UPD.BG.zeta_zero
#audit_axioms_strict UPD.BG.zeta_zero
#print axioms UPD.BG.zeta_last
#audit_axioms_strict UPD.BG.zeta_last
#print axioms UPD.BG.not_free_between
#audit_axioms_strict UPD.BG.not_free_between
#print axioms UPD.BG.exists_smaller
#audit_axioms_strict UPD.BG.exists_smaller
#print axioms UPD.BG.mem_grid_iff
#audit_axioms_strict UPD.BG.mem_grid_iff
#print axioms UPD.BG.gsite_zero
#audit_axioms_strict UPD.BG.gsite_zero
#print axioms UPD.BG.Setting.active_of_free
#audit_axioms_strict UPD.BG.Setting.active_of_free
#print axioms UPD.BG.Setting.grids_a_h
#audit_axioms_strict UPD.BG.Setting.grids_a_h
#print axioms UPD.BG.Setting.grids_a_v
#audit_axioms_strict UPD.BG.Setting.grids_a_v
#print axioms UPD.BG.Setting.grids_b
#audit_axioms_strict UPD.BG.Setting.grids_b
#print axioms UPD.BG.Setting.flags
#audit_axioms_strict UPD.BG.Setting.flags
#print axioms UPD.BG.Setting.grids_c
#audit_axioms_strict UPD.BG.Setting.grids_c
#print axioms UPD.BG.Setting.grids_d_exists
#audit_axioms_strict UPD.BG.Setting.grids_d_exists
#print axioms UPD.BG.Setting.grid_unique
#audit_axioms_strict UPD.BG.Setting.grid_unique
#print axioms UPD.BG.Setting.isRoot_iff
#audit_axioms_strict UPD.BG.Setting.isRoot_iff
#print axioms UPD.BG.Setting.isRoot_gsite_iff
#audit_axioms_strict UPD.BG.Setting.isRoot_gsite_iff
#print axioms UPD.BG.rfree_succ
#audit_axioms_strict UPD.BG.rfree_succ
#print axioms UPD.BG.rfree_inj
#audit_axioms_strict UPD.BG.rfree_inj
#print axioms UPD.BG.free_not_endpoint
#audit_axioms_strict UPD.BG.free_not_endpoint
#print axioms UPD.BG.Setting.rowM_const
#audit_axioms_strict UPD.BG.Setting.rowM_const
#print axioms UPD.BG.Setting.colM_const
#audit_axioms_strict UPD.BG.Setting.colM_const
#print axioms UPD.BG.Setting.markers_a_row
#audit_axioms_strict UPD.BG.Setting.markers_a_row
#print axioms UPD.BG.Setting.markers_a_col
#audit_axioms_strict UPD.BG.Setting.markers_a_col
#print axioms UPD.BG.Setting.markers_b_row
#audit_axioms_strict UPD.BG.Setting.markers_b_row
#print axioms UPD.BG.Setting.markers_b_col
#audit_axioms_strict UPD.BG.Setting.markers_b_col
#print axioms UPD.BG.Setting.markers_c_row
#audit_axioms_strict UPD.BG.Setting.markers_c_row
#print axioms UPD.BG.Setting.markers_c_col
#audit_axioms_strict UPD.BG.Setting.markers_c_col
#print axioms UPD.BG.carry_zero
#audit_axioms_strict UPD.BG.carry_zero
#print axioms UPD.BG.split_two_pow
#audit_axioms_strict UPD.BG.split_two_pow
#print axioms UPD.BG.mod_split
#audit_axioms_strict UPD.BG.mod_split
#print axioms UPD.BG.div_split
#audit_axioms_strict UPD.BG.div_split
#print axioms UPD.BG.carry_succ
#audit_axioms_strict UPD.BG.carry_succ
#print axioms UPD.BG.testBit_add
#audit_axioms_strict UPD.BG.testBit_add
#print axioms UPD.BG.testBit_three
#audit_axioms_strict UPD.BG.testBit_three
#print axioms UPD.BG.desc_ind
#audit_axioms_strict UPD.BG.desc_ind
#print axioms UPD.BG.lastCol
#audit_axioms_strict UPD.BG.lastCol
#print axioms UPD.BG.Setting.rules
#audit_axioms_strict UPD.BG.Setting.rules
#print axioms UPD.BG.Setting.chanH
#audit_axioms_strict UPD.BG.Setting.chanH
#print axioms UPD.BG.Setting.chanV
#audit_axioms_strict UPD.BG.Setting.chanV
#print axioms UPD.BG.Setting.chanH_some
#audit_axioms_strict UPD.BG.Setting.chanH_some
#print axioms UPD.BG.Setting.chanV_some
#audit_axioms_strict UPD.BG.Setting.chanV_some
#print axioms UPD.BG.Setting.grid_rc
#audit_axioms_strict UPD.BG.Setting.grid_rc
#print axioms UPD.BG.Setting.grid_ct_cy
#audit_axioms_strict UPD.BG.Setting.grid_ct_cy
#print axioms UPD.BG.Setting.grid_a
#audit_axioms_strict UPD.BG.Setting.grid_a
#print axioms UPD.BG.Setting.grid_cy
#audit_axioms_strict UPD.BG.Setting.grid_cy
#print axioms UPD.BG.Setting.grid_ay
#audit_axioms_strict UPD.BG.Setting.grid_ay
#print axioms UPD.BG.Setting.grid_sm
#audit_axioms_strict UPD.BG.Setting.grid_sm
#print axioms UPD.BG.Setting.grid_b
#audit_axioms_strict UPD.BG.Setting.grid_b
#print axioms UPD.BG.Setting.grid_tS
#audit_axioms_strict UPD.BG.Setting.grid_tS
#print axioms UPD.BG.Setting.grid_tS_zero
#audit_axioms_strict UPD.BG.Setting.grid_tS_zero
#print axioms UPD.BG.Setting.grid_c
#audit_axioms_strict UPD.BG.Setting.grid_c
#print axioms UPD.BG.Setting.grid_rdy
#audit_axioms_strict UPD.BG.Setting.grid_rdy
#print axioms UPD.BG.Setting.grid_d
#audit_axioms_strict UPD.BG.Setting.grid_d
#print axioms UPD.VCol.withX_bg
#audit_axioms_strict UPD.VCol.withX_bg
#print axioms UPD.BG.VColB.bg_withX
#audit_axioms_strict UPD.BG.VColB.bg_withX
#print axioms UPD.CellRec.withXY_bg
#audit_axioms_strict UPD.CellRec.withXY_bg
#print axioms UPD.BG.CellRecB.bg_withXY
#audit_axioms_strict UPD.BG.CellRecB.bg_withXY
#print axioms UPD.BG.merge_split
#audit_axioms_strict UPD.BG.merge_split
#print axioms UPD.BG.bgPart_merge
#audit_axioms_strict UPD.BG.bgPart_merge
#print axioms UPD.BG.compatible_split
#audit_axioms_strict UPD.BG.compatible_split
#print axioms UPD.BG.payPart_merge
#audit_axioms_strict UPD.BG.payPart_merge
#print axioms UPD.BG.splitEquiv
#audit_axioms_strict UPD.BG.splitEquiv
#print axioms UPD.BG.merge_bgOf_payOf
#audit_axioms_strict UPD.BG.merge_bgOf_payOf
#print axioms UPD.BG.bgOf_shift
#audit_axioms_strict UPD.BG.bgOf_shift
#print axioms UPD.BG.cE_eq_cW_iff
#audit_axioms_strict UPD.BG.cE_eq_cW_iff
#print axioms UPD.BG.option_vcol_eq_iff
#audit_axioms_strict UPD.BG.option_vcol_eq_iff
#print axioms UPD.BG.cN_eq_cS_iff
#audit_axioms_strict UPD.BG.cN_eq_cS_iff
#print axioms UPD.BG.corridor
#audit_axioms_strict UPD.BG.corridor
#print axioms UPD.BG.Line.lr_frame
#audit_axioms_strict UPD.BG.Line.lr_frame
#print axioms UPD.BG.Line.frame_of_LR
#audit_axioms_strict UPD.BG.Line.frame_of_LR
#print axioms UPD.BG.EvLine.ev_det
#audit_axioms_strict UPD.BG.EvLine.ev_det
#print axioms UPD.BG.runAt_eq
#audit_axioms_strict UPD.BG.runAt_eq
#print axioms UPD.BG.Setting.grid_ctIn
#audit_axioms_strict UPD.BG.Setting.grid_ctIn
#print axioms UPD.BG.Setting.cell_formula
#audit_axioms_strict UPD.BG.Setting.cell_formula
#print axioms UPD.BG.Setting.lE_grid
#audit_axioms_strict UPD.BG.Setting.lE_grid
#print axioms UPD.BG.Setting.lN_grid
#audit_axioms_strict UPD.BG.Setting.lN_grid
#print axioms UPD.BG.Setting.active_grid
#audit_axioms_strict UPD.BG.Setting.active_grid
#print axioms UPD.BG.Setting.k_grid
#audit_axioms_strict UPD.BG.Setting.k_grid
#print axioms UPD.BG.Setting.q_same
#audit_axioms_strict UPD.BG.Setting.q_same
#print axioms UPD.BG.Setting.VW_same
#audit_axioms_strict UPD.BG.Setting.VW_same
#print axioms UPD.BG.Setting.HW_same
#audit_axioms_strict UPD.BG.Setting.HW_same
#print axioms UPD.BG.Setting.oE_same
#audit_axioms_strict UPD.BG.Setting.oE_same
#print axioms UPD.BG.Setting.oN_same
#audit_axioms_strict UPD.BG.Setting.oN_same
#print axioms UPD.BG.Setting.oW_same
#audit_axioms_strict UPD.BG.Setting.oW_same
#print axioms UPD.BG.Setting.oS_same
#audit_axioms_strict UPD.BG.Setting.oS_same
#print axioms UPD.BG.Setting.hcarrier_iff
#audit_axioms_strict UPD.BG.Setting.hcarrier_iff
#print axioms UPD.BG.Setting.vcarrier_iff
#audit_axioms_strict UPD.BG.Setting.vcarrier_iff
#print axioms UPD.BG.Setting.active_iff
#audit_axioms_strict UPD.BG.Setting.active_iff
#print axioms UPD.BG.Setting.eE_same
#audit_axioms_strict UPD.BG.Setting.eE_same
#print axioms UPD.BG.Setting.eN_same
#audit_axioms_strict UPD.BG.Setting.eN_same
#print axioms UPD.BG.Setting.eW_same
#audit_axioms_strict UPD.BG.Setting.eW_same
#print axioms UPD.BG.Setting.eS_same
#audit_axioms_strict UPD.BG.Setting.eS_same
#print axioms UPD.BG.Setting.lE_same
#audit_axioms_strict UPD.BG.Setting.lE_same
#print axioms UPD.BG.Setting.lW_same
#audit_axioms_strict UPD.BG.Setting.lW_same
#print axioms UPD.BG.Setting.lN_same
#audit_axioms_strict UPD.BG.Setting.lN_same
#print axioms UPD.BG.Setting.lS_same
#audit_axioms_strict UPD.BG.Setting.lS_same
#print axioms UPD.BG.Setting.k_same
#audit_axioms_strict UPD.BG.Setting.k_same
#print axioms UPD.BG.Setting.rowM_same
#audit_axioms_strict UPD.BG.Setting.rowM_same
#print axioms UPD.BG.Setting.colM_same
#audit_axioms_strict UPD.BG.Setting.colM_same
#print axioms UPD.BG.Setting.background_unique
#audit_axioms_strict UPD.BG.Setting.background_unique
#print axioms UPD.BG.isQTiling_of_legal
#audit_axioms_strict UPD.BG.isQTiling_of_legal
#print axioms UPD.BG.background_rigid
#audit_axioms_strict UPD.BG.background_rigid
#print axioms UPD.BG.legal_fill
#audit_axioms_strict UPD.BG.legal_fill
#print axioms UPD.BG.freeze_a
#audit_axioms_strict UPD.BG.freeze_a
#print axioms UPD.BG.wdL_spec
#audit_axioms_strict UPD.BG.wdL_spec
#print axioms UPD.BG.wdR_spec
#audit_axioms_strict UPD.BG.wdR_spec
#print axioms UPD.BG.wdL_eq
#audit_axioms_strict UPD.BG.wdL_eq
#print axioms UPD.BG.wdR_eq
#audit_axioms_strict UPD.BG.wdR_eq
#print axioms UPD.BG.wdL_zero
#audit_axioms_strict UPD.BG.wdL_zero
#print axioms UPD.BG.wdR_zero
#audit_axioms_strict UPD.BG.wdR_zero
#print axioms UPD.BG.wdL_succ
#audit_axioms_strict UPD.BG.wdL_succ
#print axioms UPD.BG.wdR_pred
#audit_axioms_strict UPD.BG.wdR_pred
#print axioms UPD.BG.wtag_copy
#audit_axioms_strict UPD.BG.wtag_copy
#print axioms UPD.BG.wtag_left
#audit_axioms_strict UPD.BG.wtag_left
#print axioms UPD.BG.wtag_right
#audit_axioms_strict UPD.BG.wtag_right
#print axioms UPD.BG.WLine.below
#audit_axioms_strict UPD.BG.WLine.below
#print axioms UPD.BG.WLine.above
#audit_axioms_strict UPD.BG.WLine.above
#print axioms UPD.BG.WLine.toLine_o
#audit_axioms_strict UPD.BG.WLine.toLine_o
#print axioms UPD.BG.WLine.evTag_copy
#audit_axioms_strict UPD.BG.WLine.evTag_copy
#print axioms UPD.BG.WLine.wdL_pos
#audit_axioms_strict UPD.BG.WLine.wdL_pos
#print axioms UPD.BG.WLine.wdR_pos
#audit_axioms_strict UPD.BG.WLine.wdR_pos
#print axioms UPD.BG.WLine.evTag_actL
#audit_axioms_strict UPD.BG.WLine.evTag_actL
#print axioms UPD.BG.WLine.evTag_actR
#audit_axioms_strict UPD.BG.WLine.evTag_actR
#print axioms UPD.BG.WLine.evTag_wallL
#audit_axioms_strict UPD.BG.WLine.evTag_wallL
#print axioms UPD.BG.WLine.evTag_wallR
#audit_axioms_strict UPD.BG.WLine.evTag_wallR
#print axioms UPD.BG.WLine.toEvLine_toLine
#audit_axioms_strict UPD.BG.WLine.toEvLine_toLine
#print axioms UPD.BG.qphase_cfg
#audit_axioms_strict UPD.BG.qphase_cfg
#print axioms UPD.BG.rowW_L
#audit_axioms_strict UPD.BG.rowW_L
#print axioms UPD.BG.rowW_R
#audit_axioms_strict UPD.BG.rowW_R
#print axioms UPD.BG.colW_B
#audit_axioms_strict UPD.BG.colW_B
#print axioms UPD.BG.colW_T
#audit_axioms_strict UPD.BG.colW_T
#print axioms UPD.BG.cfg_hcarrier
#audit_axioms_strict UPD.BG.cfg_hcarrier
#print axioms UPD.BG.cfg_vcarrier
#audit_axioms_strict UPD.BG.cfg_vcarrier
#print axioms UPD.BG.cfg_active
#audit_axioms_strict UPD.BG.cfg_active
#print axioms UPD.BG.rowAct
#audit_axioms_strict UPD.BG.rowAct
#print axioms UPD.BG.colAct
#audit_axioms_strict UPD.BG.colAct
#print axioms UPD.BG.cfg_flags
#audit_axioms_strict UPD.BG.cfg_flags
#print axioms UPD.BG.cfg_grids_c
#audit_axioms_strict UPD.BG.cfg_grids_c
#print axioms UPD.BG.free_unique
#audit_axioms_strict UPD.BG.free_unique
#print axioms UPD.BG.HSeg_inv
#audit_axioms_strict UPD.BG.HSeg_inv
#print axioms UPD.BG.VSeg_inv
#audit_axioms_strict UPD.BG.VSeg_inv
#print axioms UPD.BG.HSeg_unique
#audit_axioms_strict UPD.BG.HSeg_unique
#print axioms UPD.BG.VSeg_unique
#audit_axioms_strict UPD.BG.VSeg_unique
#print axioms UPD.BG.GPos_unique
#audit_axioms_strict UPD.BG.GPos_unique
#print axioms UPD.BG.lEc_of
#audit_axioms_strict UPD.BG.lEc_of
#print axioms UPD.BG.lEc_none
#audit_axioms_strict UPD.BG.lEc_none
#print axioms UPD.BG.lNc_of
#audit_axioms_strict UPD.BG.lNc_of
#print axioms UPD.BG.lNc_none
#audit_axioms_strict UPD.BG.lNc_none
#print axioms UPD.BG.kF_of
#audit_axioms_strict UPD.BG.kF_of
#print axioms UPD.BG.kF_none
#audit_axioms_strict UPD.BG.kF_none
#print axioms UPD.BG.kF_xy
#audit_axioms_strict UPD.BG.kF_xy
#print axioms UPD.BG.lE_gsite
#audit_axioms_strict UPD.BG.lE_gsite
#print axioms UPD.BG.lW_gsite
#audit_axioms_strict UPD.BG.lW_gsite
#print axioms UPD.BG.lN_gsite
#audit_axioms_strict UPD.BG.lN_gsite
#print axioms UPD.BG.lS_gsite
#audit_axioms_strict UPD.BG.lS_gsite
#print axioms UPD.BG.k_gsite
#audit_axioms_strict UPD.BG.k_gsite
#print axioms UPD.BG.onColour_some
#audit_axioms_strict UPD.BG.onColour_some
#print axioms UPD.BG.onColour_none
#audit_axioms_strict UPD.BG.onColour_none
#print axioms UPD.BG.runAt_zero
#audit_axioms_strict UPD.BG.runAt_zero
#print axioms UPD.BG.runAt_succ
#audit_axioms_strict UPD.BG.runAt_succ
#print axioms UPD.BG.cfg_rules
#audit_axioms_strict UPD.BG.cfg_rules
#print axioms UPD.BG.rfree_eq_add
#audit_axioms_strict UPD.BG.rfree_eq_add
#print axioms UPD.BG.rootBelow_self
#audit_axioms_strict UPD.BG.rootBelow_self
#print axioms UPD.BG.rootBelow_pred
#audit_axioms_strict UPD.BG.rootBelow_pred
#print axioms UPD.BG.legal_of
#audit_axioms_strict UPD.BG.legal_of
#print axioms UPD.BG.evTag_none_iff
#audit_axioms_strict UPD.BG.evTag_none_iff
#print axioms UPD.BG.rowDepth_eq
#audit_axioms_strict UPD.BG.rowDepth_eq
#print axioms UPD.BG.colDepth_eq
#audit_axioms_strict UPD.BG.colDepth_eq
#print axioms UPD.BG.cfg_isRoot
#audit_axioms_strict UPD.BG.cfg_isRoot
#print axioms UPD.BG.cfg_O1
#audit_axioms_strict UPD.BG.cfg_O1
#print axioms UPD.BG.cfg_O2
#audit_axioms_strict UPD.BG.cfg_O2
#print axioms UPD.BG.cfg_E1
#audit_axioms_strict UPD.BG.cfg_E1
#print axioms UPD.BG.cfg_E2
#audit_axioms_strict UPD.BG.cfg_E2
#print axioms UPD.BG.cfg_E3
#audit_axioms_strict UPD.BG.cfg_E3
#print axioms UPD.BG.hseg_carrier
#audit_axioms_strict UPD.BG.hseg_carrier
#print axioms UPD.BG.vseg_carrier
#audit_axioms_strict UPD.BG.vseg_carrier
#print axioms UPD.BG.cfg_K1
#audit_axioms_strict UPD.BG.cfg_K1
#print axioms UPD.BG.cfg_K2
#audit_axioms_strict UPD.BG.cfg_K2
#print axioms UPD.BG.cfg_K3
#audit_axioms_strict UPD.BG.cfg_K3
#print axioms UPD.BG.cfg_Q1
#audit_axioms_strict UPD.BG.cfg_Q1
#print axioms UPD.BG.cfg_Q2
#audit_axioms_strict UPD.BG.cfg_Q2
#print axioms UPD.BG.cfg_P1
#audit_axioms_strict UPD.BG.cfg_P1
#print axioms UPD.BG.cfg_P2
#audit_axioms_strict UPD.BG.cfg_P2
#print axioms UPD.BG.cfg_P3
#audit_axioms_strict UPD.BG.cfg_P3
#print axioms UPD.BG.cfg_allowed
#audit_axioms_strict UPD.BG.cfg_allowed
#print axioms UPD.BG.cfg_matchH
#audit_axioms_strict UPD.BG.cfg_matchH
#print axioms UPD.BG.cfg_matchV
#audit_axioms_strict UPD.BG.cfg_matchV
#print axioms UPD.BG.cfg_legal
#audit_axioms_strict UPD.BG.cfg_legal
#print axioms UPD.BG.cfg_setting
#audit_axioms_strict UPD.BG.cfg_setting
#print axioms UPD.BG.bgOf_cfg
#audit_axioms_strict UPD.BG.bgOf_cfg
#print axioms UPD.BG.background_eq
#audit_axioms_strict UPD.BG.background_eq
#print axioms UPD.BG.isLegal_shift
#audit_axioms_strict UPD.BG.isLegal_shift
#print axioms UPD.BG.isQPhase_shift
#audit_axioms_strict UPD.BG.isQPhase_shift
#print axioms UPD.BG.bgMap_shift
#audit_axioms_strict UPD.BG.bgMap_shift
#print axioms UPD.BG.MLevel.of_measurable
#audit_axioms_strict UPD.BG.MLevel.of_measurable
#print axioms UPD.BG.MLevel.measurableSet
#audit_axioms_strict UPD.BG.MLevel.measurableSet
#print axioms UPD.BG.MLevel.comp
#audit_axioms_strict UPD.BG.MLevel.comp
#print axioms UPD.BG.MLevel.prod
#audit_axioms_strict UPD.BG.MLevel.prod
#print axioms UPD.BG.MLevel.ite
#audit_axioms_strict UPD.BG.MLevel.ite
#print axioms UPD.BG.MLevel.dep
#audit_axioms_strict UPD.BG.MLevel.dep
#print axioms UPD.BG.MLevel.const
#audit_axioms_strict UPD.BG.MLevel.const
#print axioms UPD.BG.MLevel.decide
#audit_axioms_strict UPD.BG.MLevel.decide
#print axioms UPD.BG.MLevel.wdL
#audit_axioms_strict UPD.BG.MLevel.wdL
#print axioms UPD.BG.MLevel.wdR
#audit_axioms_strict UPD.BG.MLevel.wdR
#print axioms UPD.BG.MLevel.wtag
#audit_axioms_strict UPD.BG.MLevel.wtag
#print axioms UPD.BG.MLevel.evTag
#audit_axioms_strict UPD.BG.MLevel.evTag
#print axioms UPD.BG.measurableSet_prefix
#audit_axioms_strict UPD.BG.measurableSet_prefix
#print axioms UPD.BG.a1_congr
#audit_axioms_strict UPD.BG.a1_congr
#print axioms UPD.BG.a2_congr
#audit_axioms_strict UPD.BG.a2_congr
#print axioms UPD.BG.inFrame_congr
#audit_axioms_strict UPD.BG.inFrame_congr
#print axioms UPD.BG.isFree_congr
#audit_axioms_strict UPD.BG.isFree_congr
#print axioms UPD.BG.freeSet_congr
#audit_axioms_strict UPD.BG.freeSet_congr
#print axioms UPD.BG.zeta_congr
#audit_axioms_strict UPD.BG.zeta_congr
#print axioms UPD.BG.rfree_congr
#audit_axioms_strict UPD.BG.rfree_congr
#print axioms UPD.BG.mlevel_qtiling
#audit_axioms_strict UPD.BG.mlevel_qtiling
#print axioms UPD.BG.mlevel_rowW
#audit_axioms_strict UPD.BG.mlevel_rowW
#print axioms UPD.BG.mlevel_colW
#audit_axioms_strict UPD.BG.mlevel_colW
#print axioms UPD.BG.measurableSet_actF
#audit_axioms_strict UPD.BG.measurableSet_actF
#print axioms UPD.BG.mlevel_oEc
#audit_axioms_strict UPD.BG.mlevel_oEc
#print axioms UPD.BG.mlevel_oNc
#audit_axioms_strict UPD.BG.mlevel_oNc
#print axioms UPD.BG.mlevel_eEc
#audit_axioms_strict UPD.BG.mlevel_eEc
#print axioms UPD.BG.mlevel_eNc
#audit_axioms_strict UPD.BG.mlevel_eNc
#print axioms UPD.BG.measurableSet_HSeg
#audit_axioms_strict UPD.BG.measurableSet_HSeg
#print axioms UPD.BG.measurableSet_VSeg
#audit_axioms_strict UPD.BG.measurableSet_VSeg
#print axioms UPD.BG.measurableSet_GPos
#audit_axioms_strict UPD.BG.measurableSet_GPos
#print axioms UPD.BG.mlevel_choose
#audit_axioms_strict UPD.BG.mlevel_choose
#print axioms UPD.BG.mlevel_lEc
#audit_axioms_strict UPD.BG.mlevel_lEc
#print axioms UPD.BG.mlevel_lNc
#audit_axioms_strict UPD.BG.mlevel_lNc
#print axioms UPD.BG.mlevel_kF
#audit_axioms_strict UPD.BG.mlevel_kF
#print axioms UPD.BG.mlevel_rowMc
#audit_axioms_strict UPD.BG.mlevel_rowMc
#print axioms UPD.BG.mlevel_colMc
#audit_axioms_strict UPD.BG.mlevel_colMc
#print axioms UPD.BG.mlevel_bgMap
#audit_axioms_strict UPD.BG.mlevel_bgMap
#print axioms UPD.BG.measurable_bgMap
#audit_axioms_strict UPD.BG.measurable_bgMap
#print axioms UPD.BG.measurable_quartersOf
#audit_axioms_strict UPD.BG.measurable_quartersOf
#print axioms UPD.BG.measurable_phaseMap
#audit_axioms_strict UPD.BG.measurable_phaseMap
#print axioms UPD.BG.measurable_bgOf
#audit_axioms_strict UPD.BG.measurable_bgOf
#print axioms UPD.BG.quartersOf_shift
#audit_axioms_strict UPD.BG.quartersOf_shift
#print axioms UPD.BG.setting_phaseMap
#audit_axioms_strict UPD.BG.setting_phaseMap
#print axioms UPD.BG.ae_legal
#audit_axioms_strict UPD.BG.ae_legal
#print axioms UPD.BG.isTILaw_quarters
#audit_axioms_strict UPD.BG.isTILaw_quarters
#print axioms UPD.BG.map_phaseMap
#audit_axioms_strict UPD.BG.map_phaseMap
#print axioms UPD.BG.ae_typical_phaseMap
#audit_axioms_strict UPD.BG.ae_typical_phaseMap
#print axioms UPD.BG.ae_bgOf
#audit_axioms_strict UPD.BG.ae_bgOf
#print axioms UPD.BG.background_law
#audit_axioms_strict UPD.BG.background_law
#print axioms UPD.BG.gibbsKernel_apply
#audit_axioms_strict UPD.BG.gibbsKernel_apply
#print axioms UPD.BG.gibbsKernel_univ_le
#audit_axioms_strict UPD.BG.gibbsKernel_univ_le
#print axioms UPD.BG.gibbsKernel_le_one
#audit_axioms_strict UPD.BG.gibbsKernel_le_one
#print axioms UPD.BG.measurable_gibbsKernel_apply
#audit_axioms_strict UPD.BG.measurable_gibbsKernel_apply
#print axioms UPD.BG.gibbsK_apply
#audit_axioms_strict UPD.BG.gibbsK_apply
#print axioms UPD.BG.lintegral_gibbsK
#audit_axioms_strict UPD.BG.lintegral_gibbsK
#print axioms UPD.BG.quarters_fill
#audit_axioms_strict UPD.BG.quarters_fill
#print axioms UPD.BG.gibbsK_inter
#audit_axioms_strict UPD.BG.gibbsK_inter
#print axioms UPD.BG.freeze_b
#audit_axioms_strict UPD.BG.freeze_b
#print axioms UPD.BG.assemble_split
#audit_axioms_strict UPD.BG.assemble_split
#print axioms UPD.BG.sum_fill_eq
#audit_axioms_strict UPD.BG.sum_fill_eq
#print axioms UPD.BG.freeze_a_product
#audit_axioms_strict UPD.BG.freeze_a_product
#print axioms UPD.BG.integral_comp_bounded
#audit_axioms_strict UPD.BG.integral_comp_bounded
#print axioms UPD.BG.isGibbs_comp
#audit_axioms_strict UPD.BG.isGibbs_comp
#print axioms UPD.BG.measurable_phase_id
#audit_axioms_strict UPD.BG.measurable_phase_id
#print axioms UPD.BG.jointLaw_fst
#audit_axioms_strict UPD.BG.jointLaw_fst
#print axioms UPD.BG.jointLaw_snd
#audit_axioms_strict UPD.BG.jointLaw_snd
#print axioms UPD.BG.jointLaw_eq
#audit_axioms_strict UPD.BG.jointLaw_eq
#print axioms UPD.BG.disintegration
#audit_axioms_strict UPD.BG.disintegration
#print axioms UPD.BG.jointLaw_prod
#audit_axioms_strict UPD.BG.jointLaw_prod
#print axioms UPD.BG.measurableSet_graph
#audit_axioms_strict UPD.BG.measurableSet_graph
#print axioms UPD.BG.ae_condLaw_graph
#audit_axioms_strict UPD.BG.ae_condLaw_graph
#print axioms UPD.BG.ae_condLaw_full
#audit_axioms_strict UPD.BG.ae_condLaw_full
#print axioms UPD.BG.jointLaw_gibbsK
#audit_axioms_strict UPD.BG.jointLaw_gibbsK
#print axioms UPD.BG.freeze_c
#audit_axioms_strict UPD.BG.freeze_c
#print axioms UPD.BG.PV.sp_spinOf
#audit_axioms_strict UPD.BG.PV.sp_spinOf
#print axioms UPD.BG.PV.wire_wireOf
#audit_axioms_strict UPD.BG.PV.wire_wireOf
#print axioms UPD.BG.PV.bit_bitOf
#audit_axioms_strict UPD.BG.PV.bit_bitOf
#print axioms UPD.BG.decode_encode
#audit_axioms_strict UPD.BG.decode_encode
#print axioms UPD.BG.encode_ok
#audit_axioms_strict UPD.BG.encode_ok
#print axioms UPD.BG.encode_decode
#audit_axioms_strict UPD.BG.encode_decode
#print axioms UPD.BG.decodeC_encodeC
#audit_axioms_strict UPD.BG.decodeC_encodeC
#print axioms UPD.BG.sitesOf_block
#audit_axioms_strict UPD.BG.sitesOf_block
#print axioms UPD.BG.siteOK_nonneg
#audit_axioms_strict UPD.BG.siteOK_nonneg
#print axioms UPD.BG.siteOK_congr
#audit_axioms_strict UPD.BG.siteOK_congr
#print axioms UPD.BG.assemble_congr
#audit_axioms_strict UPD.BG.assemble_congr
#print axioms UPD.BG.mem_block
#audit_axioms_strict UPD.BG.mem_block
#print axioms UPD.BG.fillOn_block_site
#audit_axioms_strict UPD.BG.fillOn_block_site
#print axioms UPD.BG.sum_block_eq
#audit_axioms_strict UPD.BG.sum_block_eq
#print axioms UPD.BG.frozen_expect_block
#audit_axioms_strict UPD.BG.frozen_expect_block
#print axioms UPD.BG.frozenSystem
#audit_axioms_strict UPD.BG.frozenSystem
#print axioms UPD.BG.ae_typical_addDig
#audit_axioms_strict UPD.BG.ae_typical_addDig
#print axioms UPD.BG.ae_bgMap_shift
#audit_axioms_strict UPD.BG.ae_bgMap_shift
#print axioms UPD.Gibbs.HardWeightSystem.measurable_W
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.measurable_W
#print axioms UPD.Gibbs.HardWeightSystem.measurableSet_pos
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.measurableSet_pos
#print axioms UPD.Gibbs.HardWeightSystem.isGibbs_map
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.isGibbs_map
#print axioms UPD.Gibbs.map_map_eq_self
#audit_axioms_strict UPD.Gibbs.map_map_eq_self
#print axioms UPD.Gibbs.cyl
#audit_axioms_strict UPD.Gibbs.cyl
#print axioms UPD.Gibbs.mem_cyl
#audit_axioms_strict UPD.Gibbs.mem_cyl
#print axioms UPD.Gibbs.measurableSet_cyl
#audit_axioms_strict UPD.Gibbs.measurableSet_cyl
#print axioms UPD.Gibbs.cyl_congr
#audit_axioms_strict UPD.Gibbs.cyl_congr
#print axioms UPD.Gibbs.cyl_sdiff_eq_iUnion
#audit_axioms_strict UPD.Gibbs.cyl_sdiff_eq_iUnion
#print axioms UPD.Gibbs.pairwise_disjoint_cyl_fillOn
#audit_axioms_strict UPD.Gibbs.pairwise_disjoint_cyl_fillOn
#print axioms UPD.Gibbs.measure_cyl_sdiff
#audit_axioms_strict UPD.Gibbs.measure_cyl_sdiff
#print axioms UPD.Gibbs.measureReal_cyl_sdiff
#audit_axioms_strict UPD.Gibbs.measureReal_cyl_sdiff
#print axioms UPD.Gibbs.isPiSystem_cyl
#audit_axioms_strict UPD.Gibbs.isPiSystem_cyl
#print axioms UPD.Gibbs.pi_eq_generateFrom_cyl
#audit_axioms_strict UPD.Gibbs.pi_eq_generateFrom_cyl
#print axioms UPD.Gibbs.ext_cyl
#audit_axioms_strict UPD.Gibbs.ext_cyl
#print axioms UPD.Gibbs.ext_cyl_cofinal
#audit_axioms_strict UPD.Gibbs.ext_cyl_cofinal
#print axioms UPD.Gibbs.HardWeightSystem.DB
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.DB
#print axioms UPD.Gibbs.HardWeightSystem.W_fillOn_of_mem_cyl
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.W_fillOn_of_mem_cyl
#print axioms UPD.Gibbs.HardWeightSystem.Z_of_mem_cyl
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.Z_of_mem_cyl
#print axioms UPD.Gibbs.HardWeightSystem.W_le_Z
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.W_le_Z
#print axioms UPD.Gibbs.HardWeightSystem.expect_indicator_cyl
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.expect_indicator_cyl
#print axioms UPD.Gibbs.HardWeightSystem.fd_of_isGibbs
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.fd_of_isGibbs
#print axioms UPD.Gibbs.HardWeightSystem.db_of_isGibbs
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.db_of_isGibbs
#print axioms UPD.Gibbs.HardWeightSystem.measurable_prob
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.measurable_prob
#print axioms UPD.Gibbs.HardWeightSystem.cylKernel
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.cylKernel
#print axioms UPD.Gibbs.HardWeightSystem.cylKernel_apply
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.cylKernel_apply
#print axioms UPD.Gibbs.HardWeightSystem.cylKernel_apply_set
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.cylKernel_apply_set
#print axioms UPD.Gibbs.HardWeightSystem.integral_cylKernel
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.integral_cylKernel
#print axioms UPD.Gibbs.HardWeightSystem.cylKernel_cyl
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.cylKernel_cyl
#print axioms UPD.Gibbs.HardWeightSystem.cylKernel_comp_cyl
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.cylKernel_comp_cyl
#print axioms UPD.Gibbs.HardWeightSystem.cylKernel_comp_eq
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.cylKernel_comp_eq
#print axioms UPD.Gibbs.HardWeightSystem.isGibbs_of_db
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.isGibbs_of_db
#print axioms UPD.Gibbs.FactorSystem.meets
#audit_axioms_strict UPD.Gibbs.FactorSystem.meets
#print axioms UPD.Gibbs.FactorSystem.mem_meets
#audit_axioms_strict UPD.Gibbs.FactorSystem.mem_meets
#print axioms UPD.Gibbs.FactorSystem.meets_mono
#audit_axioms_strict UPD.Gibbs.FactorSystem.meets_mono
#print axioms UPD.Gibbs.FactorSystem.W
#audit_axioms_strict UPD.Gibbs.FactorSystem.W
#print axioms UPD.Gibbs.FactorSystem.toHard
#audit_axioms_strict UPD.Gibbs.FactorSystem.toHard
#print axioms UPD.Gibbs.FactorSystem.toHard_W
#audit_axioms_strict UPD.Gibbs.FactorSystem.toHard_W
#print axioms UPD.Gibbs.FactorSystem.toHard_range
#audit_axioms_strict UPD.Gibbs.FactorSystem.toHard_range
#print axioms UPD.Gibbs.FactorSystem.φ_pos_of_W_pos
#audit_axioms_strict UPD.Gibbs.FactorSystem.φ_pos_of_W_pos
#print axioms UPD.Gibbs.FactorSystem.W_pos_of_φ_pos
#audit_axioms_strict UPD.Gibbs.FactorSystem.W_pos_of_φ_pos
#print axioms UPD.Gibbs.ElimData.Zf
#audit_axioms_strict UPD.Gibbs.ElimData.Zf
#print axioms UPD.Gibbs.ElimData.Kf
#audit_axioms_strict UPD.Gibbs.ElimData.Kf
#print axioms UPD.Gibbs.ElimData.Zf_pos'
#audit_axioms_strict UPD.Gibbs.ElimData.Zf_pos'
#print axioms UPD.Gibbs.ElimData.Kf_nonneg
#audit_axioms_strict UPD.Gibbs.ElimData.Kf_nonneg
#print axioms UPD.Gibbs.ElimData.sum_Kf
#audit_axioms_strict UPD.Gibbs.ElimData.sum_Kf
#print axioms UPD.Gibbs.ElimData.Kf_of_isEmpty
#audit_axioms_strict UPD.Gibbs.ElimData.Kf_of_isEmpty
#print axioms UPD.Gibbs.ElimData.priv
#audit_axioms_strict UPD.Gibbs.ElimData.priv
#print axioms UPD.Gibbs.ElimData.spins
#audit_axioms_strict UPD.Gibbs.ElimData.spins
#print axioms UPD.Gibbs.ElimData.edgeW
#audit_axioms_strict UPD.Gibbs.ElimData.edgeW
#print axioms UPD.Gibbs.ElimData.privSet
#audit_axioms_strict UPD.Gibbs.ElimData.privSet
#print axioms UPD.Gibbs.ElimData.mem_privSet
#audit_axioms_strict UPD.Gibbs.ElimData.mem_privSet
#print axioms UPD.Gibbs.ElimData.gamma
#audit_axioms_strict UPD.Gibbs.ElimData.gamma
#print axioms UPD.Gibbs.ElimData.gammaBar
#audit_axioms_strict UPD.Gibbs.ElimData.gammaBar
#print axioms UPD.Gibbs.ElimData.edgesOf
#audit_axioms_strict UPD.Gibbs.ElimData.edgesOf
#print axioms UPD.Gibbs.ElimData.mem_edgesOf
#audit_axioms_strict UPD.Gibbs.ElimData.mem_edgesOf
#print axioms UPD.Gibbs.ElimData.closedSet
#audit_axioms_strict UPD.Gibbs.ElimData.closedSet
#print axioms UPD.Gibbs.ElimData.inl_mem_closedSet
#audit_axioms_strict UPD.Gibbs.ElimData.inl_mem_closedSet
#print axioms UPD.Gibbs.ElimData.inr_mem_closedSet
#audit_axioms_strict UPD.Gibbs.ElimData.inr_mem_closedSet
#print axioms UPD.Gibbs.ElimData.closedSet_mono
#audit_axioms_strict UPD.Gibbs.ElimData.closedSet_mono
#print axioms UPD.Gibbs.ElimData.gamma_meets
#audit_axioms_strict UPD.Gibbs.ElimData.gamma_meets
#print axioms UPD.Gibbs.ElimData.gamma_W
#audit_axioms_strict UPD.Gibbs.ElimData.gamma_W
#print axioms UPD.Gibbs.ElimData.gammaBar_meets
#audit_axioms_strict UPD.Gibbs.ElimData.gammaBar_meets
#print axioms UPD.Gibbs.ElimData.gammaBar_W
#audit_axioms_strict UPD.Gibbs.ElimData.gammaBar_W
#print axioms UPD.Gibbs.ElimData.endsOf
#audit_axioms_strict UPD.Gibbs.ElimData.endsOf
#print axioms UPD.Gibbs.ElimData.tail_mem_endsOf
#audit_axioms_strict UPD.Gibbs.ElimData.tail_mem_endsOf
#print axioms UPD.Gibbs.ElimData.head_mem_endsOf
#audit_axioms_strict UPD.Gibbs.ElimData.head_mem_endsOf
#print axioms UPD.Gibbs.ElimData.gamma_range_subset
#audit_axioms_strict UPD.Gibbs.ElimData.gamma_range_subset
#print axioms UPD.Gibbs.ElimData.gammaBar_range_subset
#audit_axioms_strict UPD.Gibbs.ElimData.gammaBar_range_subset
#print axioms UPD.Gibbs.ElimData.vertsIn
#audit_axioms_strict UPD.Gibbs.ElimData.vertsIn
#print axioms UPD.Gibbs.ElimData.edgesIn
#audit_axioms_strict UPD.Gibbs.ElimData.edgesIn
#print axioms UPD.Gibbs.ElimData.subset_closedSet
#audit_axioms_strict UPD.Gibbs.ElimData.subset_closedSet
#print axioms UPD.Gibbs.ElimData.edgesIn_nonempty
#audit_axioms_strict UPD.Gibbs.ElimData.edgesIn_nonempty
#print axioms UPD.Gibbs.ElimData.kmeas
#audit_axioms_strict UPD.Gibbs.ElimData.kmeas
#print axioms UPD.Gibbs.ElimData.kmeas_apply
#audit_axioms_strict UPD.Gibbs.ElimData.kmeas_apply
#print axioms UPD.Gibbs.ElimData.kmeas_singleton
#audit_axioms_strict UPD.Gibbs.ElimData.kmeas_singleton
#print axioms UPD.Gibbs.ElimData.samples
#audit_axioms_strict UPD.Gibbs.ElimData.samples
#print axioms UPD.Gibbs.ElimData.assembleL
#audit_axioms_strict UPD.Gibbs.ElimData.assembleL
#print axioms UPD.Gibbs.ElimData.measurable_assembleL
#audit_axioms_strict UPD.Gibbs.ElimData.measurable_assembleL
#print axioms UPD.Gibbs.ElimData.lift
#audit_axioms_strict UPD.Gibbs.ElimData.lift
#print axioms UPD.Gibbs.ElimData.measurable_spins
#audit_axioms_strict UPD.Gibbs.ElimData.measurable_spins
#print axioms UPD.Gibbs.ElimData.map_spins_lift
#audit_axioms_strict UPD.Gibbs.ElimData.map_spins_lift
#print axioms UPD.Gibbs.ElimData.lift_cyl
#audit_axioms_strict UPD.Gibbs.ElimData.lift_cyl
#print axioms UPD.Gibbs.ElimData.lift_cyl_real
#audit_axioms_strict UPD.Gibbs.ElimData.lift_cyl_real
#print axioms UPD.Gibbs.ElimData.ext_closed
#audit_axioms_strict UPD.Gibbs.ElimData.ext_closed
#print axioms UPD.Gibbs.ElimData.endsOf_mono
#audit_axioms_strict UPD.Gibbs.ElimData.endsOf_mono
#print axioms UPD.Gibbs.ElimData.privEquiv
#audit_axioms_strict UPD.Gibbs.ElimData.privEquiv
#print axioms UPD.Gibbs.ElimData.sum_prod_priv
#audit_axioms_strict UPD.Gibbs.ElimData.sum_prod_priv
#print axioms UPD.Gibbs.ElimData.fillOn_privs_inl
#audit_axioms_strict UPD.Gibbs.ElimData.fillOn_privs_inl
#print axioms UPD.Gibbs.ElimData.sum_gamma_W_fill
#audit_axioms_strict UPD.Gibbs.ElimData.sum_gamma_W_fill
#print axioms UPD.Gibbs.ElimData.spins_preimage_cyl
#audit_axioms_strict UPD.Gibbs.ElimData.spins_preimage_cyl
#print axioms UPD.Gibbs.ElimData.closedSet_sdiff
#audit_axioms_strict UPD.Gibbs.ElimData.closedSet_sdiff
#print axioms UPD.Gibbs.ElimData.map_spins_real
#audit_axioms_strict UPD.Gibbs.ElimData.map_spins_real
#print axioms UPD.Gibbs.ElimData.ae_kmeas_pos
#audit_axioms_strict UPD.Gibbs.ElimData.ae_kmeas_pos
#print axioms UPD.Gibbs.ElimData.ae_edgeW_pos
#audit_axioms_strict UPD.Gibbs.ElimData.ae_edgeW_pos
#print axioms UPD.Gibbs.ElimData.db_alg
#audit_axioms_strict UPD.Gibbs.ElimData.db_alg
#print axioms UPD.Gibbs.ElimData.closed_cofinal
#audit_axioms_strict UPD.Gibbs.ElimData.closed_cofinal
#print axioms UPD.Gibbs.ElimData.lift_db
#audit_axioms_strict UPD.Gibbs.ElimData.lift_db
#print axioms UPD.Gibbs.ElimData.lift_isGibbs
#audit_axioms_strict UPD.Gibbs.ElimData.lift_isGibbs
#print axioms UPD.Gibbs.ElimData.isGibbs_map_spins
#audit_axioms_strict UPD.Gibbs.ElimData.isGibbs_map_spins
#print axioms UPD.Gibbs.ElimData.eq_lift
#audit_axioms_strict UPD.Gibbs.ElimData.eq_lift
#print axioms UPD.Gibbs.ElimData.elim
#audit_axioms_strict UPD.Gibbs.ElimData.elim
#print axioms UPD.Gibbs.ElimData.lift_injective
#audit_axioms_strict UPD.Gibbs.ElimData.lift_injective
#print axioms UPD.BG.toCoords
#audit_axioms_strict UPD.BG.toCoords
#print axioms UPD.BG.ofCoords
#audit_axioms_strict UPD.BG.ofCoords
#print axioms UPD.BG.measurable_toCoords
#audit_axioms_strict UPD.BG.measurable_toCoords
#print axioms UPD.BG.measurable_ofCoords
#audit_axioms_strict UPD.BG.measurable_ofCoords
#print axioms UPD.BG.ofCoords_toCoords
#audit_axioms_strict UPD.BG.ofCoords_toCoords
#print axioms UPD.BG.bgOf_ofCoords
#audit_axioms_strict UPD.BG.bgOf_ofCoords
#print axioms UPD.BG.payOf_assemble
#audit_axioms_strict UPD.BG.payOf_assemble
#print axioms UPD.BG.frozenApply_congr
#audit_axioms_strict UPD.BG.frozenApply_congr
#print axioms UPD.BG.compatible_fill
#audit_axioms_strict UPD.BG.compatible_fill
#print axioms UPD.BG.frozen_pos
#audit_axioms_strict UPD.BG.frozen_pos
#print axioms UPD.BG.siteOK_of_pos
#audit_axioms_strict UPD.BG.siteOK_of_pos
#print axioms UPD.BG.payOf_ofCoords
#audit_axioms_strict UPD.BG.payOf_ofCoords
#print axioms UPD.BG.toCoords_ofCoords
#audit_axioms_strict UPD.BG.toCoords_ofCoords
#print axioms UPD.BG.legal_ofCoords
#audit_axioms_strict UPD.BG.legal_ofCoords
#print axioms UPD.BG.setting_of_bgOf
#audit_axioms_strict UPD.BG.setting_of_bgOf
#print axioms UPD.BG.frozen_isGibbs_map
#audit_axioms_strict UPD.BG.frozen_isGibbs_map
#print axioms UPD.BG.isGibbs_map_ofCoords
#audit_axioms_strict UPD.BG.isGibbs_map_ofCoords
#print axioms UPD.BG.map_toCoords_map_ofCoords
#audit_axioms_strict UPD.BG.map_toCoords_map_ofCoords
#print axioms UPD.BG.frozen_bridge
#audit_axioms_strict UPD.BG.frozen_bridge
#print axioms UPD.Sensor.Consistent
#audit_axioms_strict UPD.Sensor.Consistent
#print axioms UPD.Sensor.bitR
#audit_axioms_strict UPD.Sensor.bitR
#print axioms UPD.Sensor.weight
#audit_axioms_strict UPD.Sensor.weight
#print axioms UPD.Sensor.switchW
#audit_axioms_strict UPD.Sensor.switchW
#print axioms UPD.Sensor.weight_eq
#audit_axioms_strict UPD.Sensor.weight_eq
#print axioms UPD.Sensor.ite_inst
#audit_axioms_strict UPD.Sensor.ite_inst
#print axioms UPD.Sensor.sum_bits
#audit_axioms_strict UPD.Sensor.sum_bits
#print axioms UPD.Sensor.sum_copies
#audit_axioms_strict UPD.Sensor.sum_copies
#print axioms UPD.Sensor.sum_free
#audit_axioms_strict UPD.Sensor.sum_free
#print axioms UPD.Sensor.sum_fiber
#audit_axioms_strict UPD.Sensor.sum_fiber
#print axioms UPD.Sensor.switchW_ff
#audit_axioms_strict UPD.Sensor.switchW_ff
#print axioms UPD.Sensor.switchW_tf
#audit_axioms_strict UPD.Sensor.switchW_tf
#print axioms UPD.Sensor.switchW_ft
#audit_axioms_strict UPD.Sensor.switchW_ft
#print axioms UPD.Sensor.switchW_tt
#audit_axioms_strict UPD.Sensor.switchW_tt
#print axioms UPD.Sensor.sum_weight
#audit_axioms_strict UPD.Sensor.sum_weight
#print axioms UPD.Sensor.pay_sum
#audit_axioms_strict UPD.Sensor.pay_sum
#print axioms UPD.Sensor.coupling
#audit_axioms_strict UPD.Sensor.coupling
#print axioms UPD.Sensor.weight_nonneg
#audit_axioms_strict UPD.Sensor.weight_nonneg
#print axioms UPD.Sensor.sum_weight_pos
#audit_axioms_strict UPD.Sensor.sum_weight_pos
#print axioms UPD.Gibbs.WeightSystem.toHard
#audit_axioms_strict UPD.Gibbs.WeightSystem.toHard
#print axioms UPD.Gibbs.WeightSystem.toHard_W
#audit_axioms_strict UPD.Gibbs.WeightSystem.toHard_W
#print axioms UPD.Gibbs.WeightSystem.toHard_expect
#audit_axioms_strict UPD.Gibbs.WeightSystem.toHard_expect
#print axioms UPD.Gibbs.WeightSystem.isDLR_iff_isGibbs_toHard
#audit_axioms_strict UPD.Gibbs.WeightSystem.isDLR_iff_isGibbs_toHard
#print axioms UPD.Gibbs.fillOn_recode
#audit_axioms_strict UPD.Gibbs.fillOn_recode
#print axioms UPD.Gibbs.sum_fillOn_recode
#audit_axioms_strict UPD.Gibbs.sum_fillOn_recode
#print axioms UPD.Gibbs.expect_recode
#audit_axioms_strict UPD.Gibbs.expect_recode
#print axioms UPD.Gibbs.measurable_recode
#audit_axioms_strict UPD.Gibbs.measurable_recode
#print axioms UPD.Gibbs.measurable_decode
#audit_axioms_strict UPD.Gibbs.measurable_decode
#print axioms UPD.Gibbs.isGibbs_map_recode
#audit_axioms_strict UPD.Gibbs.isGibbs_map_recode
#print axioms UPD.Gibbs.isDLR_map_decode
#audit_axioms_strict UPD.Gibbs.isDLR_map_decode
#print axioms UPD.Gibbs.isGibbs_iff_recode
#audit_axioms_strict UPD.Gibbs.isGibbs_iff_recode
#print axioms UPD.Gibbs.HardWeightSystem.Pos
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.Pos
#print axioms UPD.Gibbs.HardWeightSystem.pos_of_pos
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.pos_of_pos
#print axioms UPD.Gibbs.HardWeightSystem.mapEquiv
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.mapEquiv
#print axioms UPD.Gibbs.HardWeightSystem.fillOn_map
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.fillOn_map
#print axioms UPD.Gibbs.HardWeightSystem.expect_eq_of_ratio
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.expect_eq_of_ratio
#print axioms UPD.Gibbs.HardWeightSystem.measurable_comp_equiv
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.measurable_comp_equiv
#print axioms UPD.Gibbs.HardWeightSystem.isGibbs_iff_of_ratio
#audit_axioms_strict UPD.Gibbs.HardWeightSystem.isGibbs_iff_of_ratio
#print axioms UPD.Gibbs.shift_shift
#audit_axioms_strict UPD.Gibbs.shift_shift
#print axioms UPD.Gibbs.shift_zero_apply
#audit_axioms_strict UPD.Gibbs.shift_zero_apply
#print axioms UPD.Gibbs.image_add_image_sub
#audit_axioms_strict UPD.Gibbs.image_add_image_sub
#print axioms UPD.Gibbs.image_sub_image_add
#audit_axioms_strict UPD.Gibbs.image_sub_image_add
#print axioms UPD.Gibbs.mem_image_add
#audit_axioms_strict UPD.Gibbs.mem_image_add
#print axioms UPD.Gibbs.isLegal_shift_iff
#audit_axioms_strict UPD.Gibbs.isLegal_shift_iff
#print axioms UPD.Gibbs.energy_shift
#audit_axioms_strict UPD.Gibbs.energy_shift
#print axioms UPD.Gibbs.kernelApply_shift
#audit_axioms_strict UPD.Gibbs.kernelApply_shift
#print axioms UPD.Gibbs.measurable_shiftConfig
#audit_axioms_strict UPD.Gibbs.measurable_shiftConfig
#print axioms UPD.Gibbs.map_shift_map_shift
#audit_axioms_strict UPD.Gibbs.map_shift_map_shift
#print axioms UPD.Gibbs.map_shift_zero
#audit_axioms_strict UPD.Gibbs.map_shift_zero
#print axioms UPD.Gibbs.isTranslationInvariantMeasure_of_e1_e2
#audit_axioms_strict UPD.Gibbs.isTranslationInvariantMeasure_of_e1_e2
#print axioms UPD.Gibbs.isGibbs_map_shift
#audit_axioms_strict UPD.Gibbs.isGibbs_map_shift
#print axioms UPD.Gibbs.isGibbs_finsetAvg
#audit_axioms_strict UPD.Gibbs.isGibbs_finsetAvg
#print axioms UPD.Gibbs.natSite
#audit_axioms_strict UPD.Gibbs.natSite
#print axioms UPD.Gibbs.natSite_injective
#audit_axioms_strict UPD.Gibbs.natSite_injective
#print axioms UPD.Gibbs.avgBox
#audit_axioms_strict UPD.Gibbs.avgBox
#print axioms UPD.Gibbs.card_avgBox
#audit_axioms_strict UPD.Gibbs.card_avgBox
#print axioms UPD.Gibbs.avgBox_nonempty
#audit_axioms_strict UPD.Gibbs.avgBox_nonempty
#print axioms UPD.Gibbs.sum_avgBox
#audit_axioms_strict UPD.Gibbs.sum_avgBox
#print axioms UPD.Gibbs.abs_sum_avgBox_shift_sub_le
#audit_axioms_strict UPD.Gibbs.abs_sum_avgBox_shift_sub_le
#print axioms UPD.Gibbs.avgMeasure
#audit_axioms_strict UPD.Gibbs.avgMeasure
#print axioms UPD.Gibbs.boxAvg
#audit_axioms_strict UPD.Gibbs.boxAvg
#print axioms UPD.Gibbs.isProbabilityMeasure_avgMeasure
#audit_axioms_strict UPD.Gibbs.isProbabilityMeasure_avgMeasure
#print axioms UPD.Gibbs.avgPM
#audit_axioms_strict UPD.Gibbs.avgPM
#print axioms UPD.Gibbs.integral_avgMeasure
#audit_axioms_strict UPD.Gibbs.integral_avgMeasure
#print axioms UPD.Gibbs.measureReal_avgMeasure
#audit_axioms_strict UPD.Gibbs.measureReal_avgMeasure
#print axioms UPD.Gibbs.abs_avgMeasure_shift_sub_le
#audit_axioms_strict UPD.Gibbs.abs_avgMeasure_shift_sub_le
#print axioms UPD.Gibbs.le_boxAvg
#audit_axioms_strict UPD.Gibbs.le_boxAvg
#print axioms UPD.Gibbs.boxAvg_le
#audit_axioms_strict UPD.Gibbs.boxAvg_le
#print axioms UPD.Gibbs.isGibbs_avgMeasure
#audit_axioms_strict UPD.Gibbs.isGibbs_avgMeasure
#print axioms UPD.Gibbs.mem_of_clusterPt
#audit_axioms_strict UPD.Gibbs.mem_of_clusterPt
#print axioms UPD.Gibbs.cyl_local
#audit_axioms_strict UPD.Gibbs.cyl_local
#print axioms UPD.Gibbs.continuous_of_local
#audit_axioms_strict UPD.Gibbs.continuous_of_local
#print axioms UPD.Gibbs.continuous_integral_of_continuous
#audit_axioms_strict UPD.Gibbs.continuous_integral_of_continuous
#print axioms UPD.Gibbs.continuous_measureReal_of_local
#audit_axioms_strict UPD.Gibbs.continuous_measureReal_of_local
#print axioms UPD.Gibbs.isGibbs_of_clusterPt
#audit_axioms_strict UPD.Gibbs.isGibbs_of_clusterPt
#print axioms UPD.Gibbs.isTranslationInvariantMeasure_of_clusterPt
#audit_axioms_strict UPD.Gibbs.isTranslationInvariantMeasure_of_clusterPt
#print axioms UPD.Gibbs.bounded_of_continuous
#audit_axioms_strict UPD.Gibbs.bounded_of_continuous
#print axioms UPD.Gibbs.exists_ti_gibbs_avg_of_continuous
#audit_axioms_strict UPD.Gibbs.exists_ti_gibbs_avg_of_continuous
#print axioms UPD.Gibbs.exists_ti_gibbs_avg₂_of_continuous
#audit_axioms_strict UPD.Gibbs.exists_ti_gibbs_avg₂_of_continuous
#print axioms UPD.Gibbs.exists_ti_gibbs_avg
#audit_axioms_strict UPD.Gibbs.exists_ti_gibbs_avg
#print axioms UPD.Gibbs.exists_ti_gibbs_avg₂
#audit_axioms_strict UPD.Gibbs.exists_ti_gibbs_avg₂
#print axioms UPD.Gibbs.exists_ti_gibbs
#audit_axioms_strict UPD.Gibbs.exists_ti_gibbs
#print axioms UPD.BG.root_inj'
#audit_axioms_strict UPD.BG.root_inj'
#print axioms UPD.BG.root_inj
#audit_axioms_strict UPD.BG.root_inj
#print axioms UPD.BG.rootData
#audit_axioms_strict UPD.BG.rootData
#print axioms UPD.BG.rootData_eq_some_iff
#audit_axioms_strict UPD.BG.rootData_eq_some_iff
#print axioms UPD.BG.rootData_root
#audit_axioms_strict UPD.BG.rootData_root
#print axioms UPD.BG.rootData_cases
#audit_axioms_strict UPD.BG.rootData_cases
#print axioms UPD.BG.gNbr
#audit_axioms_strict UPD.BG.gNbr
#print axioms UPD.BG.gNbr_root
#audit_axioms_strict UPD.BG.gNbr_root
#print axioms UPD.BG.mem_gNbr
#audit_axioms_strict UPD.BG.mem_gNbr
#print axioms UPD.BG.gNbr_symm
#audit_axioms_strict UPD.BG.gNbr_symm
#print axioms UPD.BG.gNbr_irrefl
#audit_axioms_strict UPD.BG.gNbr_irrefl
#print axioms UPD.BG.depthOf
#audit_axioms_strict UPD.BG.depthOf
#print axioms UPD.BG.depthOf_root
#audit_axioms_strict UPD.BG.depthOf_root
#print axioms UPD.BG.Jc_nonneg
#audit_axioms_strict UPD.BG.Jc_nonneg
#print axioms UPD.BG.Jc_bc_nonneg
#audit_axioms_strict UPD.BG.Jc_bc_nonneg
#print axioms UPD.BG.siteJ
#audit_axioms_strict UPD.BG.siteJ
#print axioms UPD.BG.siteJ_root
#audit_axioms_strict UPD.BG.siteJ_root
#print axioms UPD.BG.siteJ_nonneg
#audit_axioms_strict UPD.BG.siteJ_nonneg
#print axioms UPD.BG.siteJ_cases
#audit_axioms_strict UPD.BG.siteJ_cases
#print axioms UPD.BG.gJ
#audit_axioms_strict UPD.BG.gJ
#print axioms UPD.BG.Gamma
#audit_axioms_strict UPD.BG.Gamma
#print axioms UPD.BG.mem_Gamma_nbr
#audit_axioms_strict UPD.BG.mem_Gamma_nbr
#print axioms UPD.BG.Gamma_J_root
#audit_axioms_strict UPD.BG.Gamma_J_root
#print axioms UPD.BG.Gamma_J_cases
#audit_axioms_strict UPD.BG.Gamma_J_cases
#print axioms UPD.BG.card_Gamma_nbr_le
#audit_axioms_strict UPD.BG.card_Gamma_nbr_le
#print axioms UPD.BG.isComponentMap_depthOf
#audit_axioms_strict UPD.BG.isComponentMap_depthOf
#print axioms UPD.BG.rootMap
#audit_axioms_strict UPD.BG.rootMap
#print axioms UPD.BG.rootMap_bijective
#audit_axioms_strict UPD.BG.rootMap_bijective
#print axioms UPD.BG.squareIso
#audit_axioms_strict UPD.BG.squareIso
#print axioms UPD.BG.squareIso_e
#audit_axioms_strict UPD.BG.squareIso_e
#print axioms UPD.BG.gB
#audit_axioms_strict UPD.BG.gB
#print axioms UPD.BG.RCell
#audit_axioms_strict UPD.BG.RCell
#print axioms UPD.BG.RChan
#audit_axioms_strict UPD.BG.RChan
#print axioms UPD.BG.colRoot
#audit_axioms_strict UPD.BG.colRoot
#print axioms UPD.BG.kxX
#audit_axioms_strict UPD.BG.kxX
#print axioms UPD.BG.lNxX
#audit_axioms_strict UPD.BG.lNxX
#print axioms UPD.BG.payX
#audit_axioms_strict UPD.BG.payX
#print axioms UPD.BG.P3X
#audit_axioms_strict UPD.BG.P3X
#print axioms UPD.BG.rootBelow_le
#audit_axioms_strict UPD.BG.rootBelow_le
#print axioms UPD.BG.rootBelow_eq
#audit_axioms_strict UPD.BG.rootBelow_eq
#print axioms UPD.BG.rfree_succ_eq
#audit_axioms_strict UPD.BG.rfree_succ_eq
#print axioms UPD.BG.rootBelow_of_frame
#audit_axioms_strict UPD.BG.rootBelow_of_frame
#print axioms UPD.BG.wire_line
#audit_axioms_strict UPD.BG.wire_line
#print axioms UPD.BG.const_up
#audit_axioms_strict UPD.BG.const_up
#print axioms UPD.BG.zeta_le_zeta
#audit_axioms_strict UPD.BG.zeta_le_zeta
#print axioms UPD.BG.exists_zeta_interval
#audit_axioms_strict UPD.BG.exists_zeta_interval
#print axioms UPD.BG.colRoot_gsite
#audit_axioms_strict UPD.BG.colRoot_gsite
#print axioms UPD.BG.kxX_gsite
#audit_axioms_strict UPD.BG.kxX_gsite
#print axioms UPD.BG.kxX_eq_false
#audit_axioms_strict UPD.BG.kxX_eq_false
#print axioms UPD.BG.kxX_gpos
#audit_axioms_strict UPD.BG.kxX_gpos
#print axioms UPD.BG.kxX_of_not_gpos
#audit_axioms_strict UPD.BG.kxX_of_not_gpos
#print axioms UPD.BG.lNxX_col
#audit_axioms_strict UPD.BG.lNxX_col
#print axioms UPD.BG.lNxX_eq_false
#audit_axioms_strict UPD.BG.lNxX_eq_false
#print axioms UPD.BG.lNxX_vseg
#audit_axioms_strict UPD.BG.lNxX_vseg
#print axioms UPD.BG.lNxX_of_not_vseg
#audit_axioms_strict UPD.BG.lNxX_of_not_vseg
#print axioms UPD.BG.wEc_arm
#audit_axioms_strict UPD.BG.wEc_arm
#print axioms UPD.BG.wEc_unmarked
#audit_axioms_strict UPD.BG.wEc_unmarked
#print axioms UPD.BG.wNc_arm
#audit_axioms_strict UPD.BG.wNc_arm
#print axioms UPD.BG.wNc_unmarked
#audit_axioms_strict UPD.BG.wNc_unmarked
#print axioms UPD.BG.payVal_ext
#audit_axioms_strict UPD.BG.payVal_ext
#print axioms UPD.BG.compatible_payX
#audit_axioms_strict UPD.BG.compatible_payX
#print axioms UPD.BG.xOf_lNc
#audit_axioms_strict UPD.BG.xOf_lNc
#print axioms UPD.BG.kF_x
#audit_axioms_strict UPD.BG.kF_x
#print axioms UPD.BG.kF_y
#audit_axioms_strict UPD.BG.kF_y
#print axioms UPD.BG.payOf_cfg
#audit_axioms_strict UPD.BG.payOf_cfg
#print axioms UPD.BG.cfg_eq_assemble
#audit_axioms_strict UPD.BG.cfg_eq_assemble
#print axioms UPD.BG.cfg_site
#audit_axioms_strict UPD.BG.cfg_site
#print axioms UPD.BG.merge_lS
#audit_axioms_strict UPD.BG.merge_lS
#print axioms UPD.BG.merge_lN
#audit_axioms_strict UPD.BG.merge_lN
#print axioms UPD.BG.merge_k
#audit_axioms_strict UPD.BG.merge_k
#print axioms UPD.BG.onColour_map
#audit_axioms_strict UPD.BG.onColour_map
#print axioms UPD.BG.C0_merge
#audit_axioms_strict UPD.BG.C0_merge
#print axioms UPD.BG.C1_merge
#audit_axioms_strict UPD.BG.C1_merge
#print axioms UPD.BG.C2_merge
#audit_axioms_strict UPD.BG.C2_merge
#print axioms UPD.BG.C3_merge
#audit_axioms_strict UPD.BG.C3_merge
#print axioms UPD.BG.C4_merge
#audit_axioms_strict UPD.BG.C4_merge
#print axioms UPD.BG.C5_merge
#audit_axioms_strict UPD.BG.C5_merge
#print axioms UPD.BG.C6_merge
#audit_axioms_strict UPD.BG.C6_merge
#print axioms UPD.BG.C7_merge
#audit_axioms_strict UPD.BG.C7_merge
#print axioms UPD.BG.P1_merge
#audit_axioms_strict UPD.BG.P1_merge
#print axioms UPD.BG.P2_merge
#audit_axioms_strict UPD.BG.P2_merge
#print axioms UPD.BG.allowed_merge
#audit_axioms_strict UPD.BG.allowed_merge
#print axioms UPD.BG.bool_and3
#audit_axioms_strict UPD.BG.bool_and3
#print axioms UPD.BG.bgMap_k_gsite
#audit_axioms_strict UPD.BG.bgMap_k_gsite
#print axioms UPD.BG.bgMap_lN_gsite
#audit_axioms_strict UPD.BG.bgMap_lN_gsite
#print axioms UPD.BG.payX_kx_grid
#audit_axioms_strict UPD.BG.payX_kx_grid
#print axioms UPD.BG.payX_lNx_grid
#audit_axioms_strict UPD.BG.payX_lNx_grid
#print axioms UPD.BG.payX_lSx_grid
#audit_axioms_strict UPD.BG.payX_lSx_grid
#print axioms UPD.BG.allowed_payX
#audit_axioms_strict UPD.BG.allowed_payX
#print axioms UPD.BG.matchH_payX
#audit_axioms_strict UPD.BG.matchH_payX
#print axioms UPD.BG.matchV_payX
#audit_axioms_strict UPD.BG.matchV_payX
#print axioms UPD.BG.legal_payX
#audit_axioms_strict UPD.BG.legal_payX
#print axioms UPD.BG.wE_legal
#audit_axioms_strict UPD.BG.wE_legal
#print axioms UPD.BG.wN_legal
#audit_axioms_strict UPD.BG.wN_legal
#print axioms UPD.BG.lN_chan
#audit_axioms_strict UPD.BG.lN_chan
#print axioms UPD.BG.lNx_grid
#audit_axioms_strict UPD.BG.lNx_grid
#print axioms UPD.BG.kx_col
#audit_axioms_strict UPD.BG.kx_col
#print axioms UPD.BG.kx_root
#audit_axioms_strict UPD.BG.kx_root
#print axioms UPD.BG.kx_legal
#audit_axioms_strict UPD.BG.kx_legal
#print axioms UPD.BG.lNx_legal
#audit_axioms_strict UPD.BG.lNx_legal
#print axioms UPD.BG.bool_y
#audit_axioms_strict UPD.BG.bool_y
#print axioms UPD.BG.payOf_eq_payX
#audit_axioms_strict UPD.BG.payOf_eq_payX
#print axioms UPD.BG.p3X_of_legal
#audit_axioms_strict UPD.BG.p3X_of_legal
#print axioms UPD.BG.legal_iff_payX
#audit_axioms_strict UPD.BG.legal_iff_payX
#print axioms UPD.BG.REdge
#audit_axioms_strict UPD.BG.REdge
#print axioms UPD.BG.Ed
#audit_axioms_strict UPD.BG.Ed
#print axioms UPD.BG.rhead
#audit_axioms_strict UPD.BG.rhead
#print axioms UPD.BG.rtail
#audit_axioms_strict UPD.BG.rtail
#print axioms UPD.BG.etail
#audit_axioms_strict UPD.BG.etail
#print axioms UPD.BG.ehead
#audit_axioms_strict UPD.BG.ehead
#print axioms UPD.BG.armPred
#audit_axioms_strict UPD.BG.armPred
#print axioms UPD.BG.InPair
#audit_axioms_strict UPD.BG.InPair
#print axioms UPD.BG.sensPred
#audit_axioms_strict UPD.BG.sensPred
#print axioms UPD.BG.privPred
#audit_axioms_strict UPD.BG.privPred
#print axioms UPD.BG.idx_unique
#audit_axioms_strict UPD.BG.idx_unique
#print axioms UPD.BG.idx_unique'
#audit_axioms_strict UPD.BG.idx_unique'
#print axioms UPD.BG.zeta_mem_window
#audit_axioms_strict UPD.BG.zeta_mem_window
#print axioms UPD.BG.zeta_last_lt
#audit_axioms_strict UPD.BG.zeta_last_lt
#print axioms UPD.BG.zeta_first
#audit_axioms_strict UPD.BG.zeta_first
#print axioms UPD.BG.col_window
#audit_axioms_strict UPD.BG.col_window
#print axioms UPD.BG.gsite_inj
#audit_axioms_strict UPD.BG.gsite_inj
#print axioms UPD.BG.inPair_unique
#audit_axioms_strict UPD.BG.inPair_unique
#print axioms UPD.BG.privPred_unique
#audit_axioms_strict UPD.BG.privPred_unique
#print axioms UPD.BG.not_privPred_spin
#audit_axioms_strict UPD.BG.not_privPred_spin
#print axioms UPD.BG.owner
#audit_axioms_strict UPD.BG.owner
#print axioms UPD.BG.owner_of
#audit_axioms_strict UPD.BG.owner_of
#print axioms UPD.BG.owner_of_not
#audit_axioms_strict UPD.BG.owner_of_not
#print axioms UPD.BG.privPred_of_owner
#audit_axioms_strict UPD.BG.privPred_of_owner
#print axioms UPD.BG.of_owner_inl
#audit_axioms_strict UPD.BG.of_owner_inl
#print axioms UPD.BG.Q
#audit_axioms_strict UPD.BG.Q
#print axioms UPD.BG.rfree_pred_le
#audit_axioms_strict UPD.BG.rfree_pred_le
#print axioms UPD.BG.privPred_finite
#audit_axioms_strict UPD.BG.privPred_finite
#print axioms UPD.BG.instDecEqSigmaQ
#audit_axioms_strict UPD.BG.instDecEqSigmaQ
#print axioms UPD.BG.relabel
#audit_axioms_strict UPD.BG.relabel
#print axioms UPD.BG.relabel_spin
#audit_axioms_strict UPD.BG.relabel_spin
#print axioms UPD.BG.relabel_of
#audit_axioms_strict UPD.BG.relabel_of
#print axioms UPD.BG.rootIdx
#audit_axioms_strict UPD.BG.rootIdx
#print axioms UPD.BG.edgesAt
#audit_axioms_strict UPD.BG.edgesAt
#print axioms UPD.BG.rootIdx_root
#audit_axioms_strict UPD.BG.rootIdx_root
#print axioms UPD.BG.rootIdx_none
#audit_axioms_strict UPD.BG.rootIdx_none
#print axioms UPD.BG.mem_edgesAt
#audit_axioms_strict UPD.BG.mem_edgesAt
#print axioms UPD.BG.fixedVal
#audit_axioms_strict UPD.BG.fixedVal
#print axioms UPD.BG.swv
#audit_axioms_strict UPD.BG.swv
#print axioms UPD.BG.tgt
#audit_axioms_strict UPD.BG.tgt
#print axioms UPD.BG.iMinus
#audit_axioms_strict UPD.BG.iMinus
#print axioms UPD.BG.iPlus
#audit_axioms_strict UPD.BG.iPlus
#print axioms UPD.BG.Good
#audit_axioms_strict UPD.BG.Good
#print axioms UPD.BG.p0
#audit_axioms_strict UPD.BG.p0
#print axioms UPD.BG.chW
#audit_axioms_strict UPD.BG.chW
#print axioms UPD.BG.Wf
#audit_axioms_strict UPD.BG.Wf
#print axioms UPD.BG.Wf_nonneg
#audit_axioms_strict UPD.BG.Wf_nonneg
#print axioms UPD.BG.zeta0
#audit_axioms_strict UPD.BG.zeta0
#print axioms UPD.BG.swv_zeta0
#audit_axioms_strict UPD.BG.swv_zeta0
#print axioms UPD.BG.good_zeta0
#audit_axioms_strict UPD.BG.good_zeta0
#print axioms UPD.BG.Zf_pos
#audit_axioms_strict UPD.BG.Zf_pos
#print axioms UPD.BG.elimData
#audit_axioms_strict UPD.BG.elimData
#print axioms UPD.BG.idxOf
#audit_axioms_strict UPD.BG.idxOf
#print axioms UPD.BG.idxOf_spec
#audit_axioms_strict UPD.BG.idxOf_spec
#print axioms UPD.BG.arm_wE
#audit_axioms_strict UPD.BG.arm_wE
#print axioms UPD.BG.arm_wW
#audit_axioms_strict UPD.BG.arm_wW
#print axioms UPD.BG.arm_wN
#audit_axioms_strict UPD.BG.arm_wN
#print axioms UPD.BG.arm_wS
#audit_axioms_strict UPD.BG.arm_wS
#print axioms UPD.BG.dirOf
#audit_axioms_strict UPD.BG.dirOf
#print axioms UPD.BG.inPair_dirOf
#audit_axioms_strict UPD.BG.inPair_dirOf
#print axioms UPD.BG.sens_gsite
#audit_axioms_strict UPD.BG.sens_gsite
#print axioms UPD.BG.sens_lNx
#audit_axioms_strict UPD.BG.sens_lNx
#print axioms UPD.BG.sens_lSx
#audit_axioms_strict UPD.BG.sens_lSx
#print axioms UPD.BG.payX_site
#audit_axioms_strict UPD.BG.payX_site
#print axioms UPD.BG.tgtX
#audit_axioms_strict UPD.BG.tgtX
#print axioms UPD.BG.rhead_eq
#audit_axioms_strict UPD.BG.rhead_eq
#print axioms UPD.BG.payX_priv
#audit_axioms_strict UPD.BG.payX_priv
#print axioms UPD.BG.sens_head
#audit_axioms_strict UPD.BG.sens_head
#print axioms UPD.BG.sens_root
#audit_axioms_strict UPD.BG.sens_root
#print axioms UPD.BG.ready_of_sens
#audit_axioms_strict UPD.BG.ready_of_sens
#print axioms UPD.BG.swv_of
#audit_axioms_strict UPD.BG.swv_of
#print axioms UPD.BG.swv_of_not
#audit_axioms_strict UPD.BG.swv_of_not
#print axioms UPD.BG.inPair_iMinus
#audit_axioms_strict UPD.BG.inPair_iMinus
#print axioms UPD.BG.inPair_iPlus
#audit_axioms_strict UPD.BG.inPair_iPlus
#print axioms UPD.BG.coords_eq
#audit_axioms_strict UPD.BG.coords_eq
#print axioms UPD.BG.frozen_pos_iff
#audit_axioms_strict UPD.BG.frozen_pos_iff
#print axioms UPD.BG.gamma_pos_iff
#audit_axioms_strict UPD.BG.gamma_pos_iff
#print axioms UPD.BG.tgt_eq_tgtX
#audit_axioms_strict UPD.BG.tgt_eq_tgtX
#print axioms UPD.BG.pos_iff
#audit_axioms_strict UPD.BG.pos_iff
#print axioms UPD.BG.phi_legal
#audit_axioms_strict UPD.BG.phi_legal
#print axioms UPD.BG.energy_legal
#audit_axioms_strict UPD.BG.energy_legal
#print axioms UPD.BG.charge_assemble
#audit_axioms_strict UPD.BG.charge_assemble
#print axioms UPD.BG.Fsum
#audit_axioms_strict UPD.BG.Fsum
#print axioms UPD.BG.Gsum
#audit_axioms_strict UPD.BG.Gsum
#print axioms UPD.BG.frozenW_eq
#audit_axioms_strict UPD.BG.frozenW_eq
#print axioms UPD.BG.gammaW_eq
#audit_axioms_strict UPD.BG.gammaW_eq
#print axioms UPD.BG.Fsum_sub
#audit_axioms_strict UPD.BG.Fsum_sub
#print axioms UPD.BG.chW_spin
#audit_axioms_strict UPD.BG.chW_spin
#print axioms UPD.BG.Gsum_sub
#audit_axioms_strict UPD.BG.Gsum_sub
#print axioms UPD.BG.ratio
#audit_axioms_strict UPD.BG.ratio
#print axioms UPD.BG.pay_factor
#audit_axioms_strict UPD.BG.pay_factor
#print axioms UPD.BG.Zf_site
#audit_axioms_strict UPD.BG.Zf_site
#print axioms UPD.BG.chW_nonready
#audit_axioms_strict UPD.BG.chW_nonready
#print axioms UPD.BG.good_nonready
#audit_axioms_strict UPD.BG.good_nonready
#print axioms UPD.BG.Zf_nonready
#audit_axioms_strict UPD.BG.Zf_nonready
#print axioms UPD.BG.swComp
#audit_axioms_strict UPD.BG.swComp
#print axioms UPD.BG.swSide
#audit_axioms_strict UPD.BG.swSide
#print axioms UPD.BG.swSide_swComp
#audit_axioms_strict UPD.BG.swSide_swComp
#print axioms UPD.BG.swComp_swSide
#audit_axioms_strict UPD.BG.swComp_swSide
#print axioms UPD.BG.inPair_swComp
#audit_axioms_strict UPD.BG.inPair_swComp
#print axioms UPD.BG.swComp_zero
#audit_axioms_strict UPD.BG.swComp_zero
#print axioms UPD.BG.swComp_one
#audit_axioms_strict UPD.BG.swComp_one
#print axioms UPD.BG.swSide_iMinus
#audit_axioms_strict UPD.BG.swSide_iMinus
#print axioms UPD.BG.swSide_iPlus
#audit_axioms_strict UPD.BG.swSide_iPlus
#print axioms UPD.BG.Nd_ge_of_ready
#audit_axioms_strict UPD.BG.Nd_ge_of_ready
#print axioms UPD.BG.gsite_col_inj
#audit_axioms_strict UPD.BG.gsite_col_inj
#print axioms UPD.BG.jOf
#audit_axioms_strict UPD.BG.jOf
#print axioms UPD.BG.jOf_gsite
#audit_axioms_strict UPD.BG.jOf_gsite
#print axioms UPD.BG.sensL
#audit_axioms_strict UPD.BG.sensL
#print axioms UPD.BG.gB_gsite
#audit_axioms_strict UPD.BG.gB_gsite
#print axioms UPD.BG.active_merge
#audit_axioms_strict UPD.BG.active_merge
#print axioms UPD.BG.fW_merge
#audit_axioms_strict UPD.BG.fW_merge
#print axioms UPD.BG.chW_gsite
#audit_axioms_strict UPD.BG.chW_gsite
#print axioms UPD.BG.yAt
#audit_axioms_strict UPD.BG.yAt
#print axioms UPD.BG.yAt_of
#audit_axioms_strict UPD.BG.yAt_of
#print axioms UPD.BG.yAt_val
#audit_axioms_strict UPD.BG.yAt_val
#print axioms UPD.BG.rdBit
#audit_axioms_strict UPD.BG.rdBit
#print axioms UPD.BG.rdBit_of
#audit_axioms_strict UPD.BG.rdBit_of
#print axioms UPD.BG.sens_mem
#audit_axioms_strict UPD.BG.sens_mem
#print axioms UPD.BG.sens_inv
#audit_axioms_strict UPD.BG.sens_inv
#print axioms UPD.BG.sens_root'
#audit_axioms_strict UPD.BG.sens_root'
#print axioms UPD.BG.toCfg
#audit_axioms_strict UPD.BG.toCfg
#print axioms UPD.BG.ofCfg
#audit_axioms_strict UPD.BG.ofCfg
#print axioms UPD.BG.toCfg_switch
#audit_axioms_strict UPD.BG.toCfg_switch
#print axioms UPD.BG.swv_ofCfg
#audit_axioms_strict UPD.BG.swv_ofCfg
#print axioms UPD.BG.toCfg_ofCfg
#audit_axioms_strict UPD.BG.toCfg_ofCfg
#print axioms UPD.BG.ofCfg_toCfg
#audit_axioms_strict UPD.BG.ofCfg_toCfg
#print axioms UPD.BG.bit_and_iff
#audit_axioms_strict UPD.BG.bit_and_iff
#print axioms UPD.BG.tgt_ofCfg_iff
#audit_axioms_strict UPD.BG.tgt_ofCfg_iff
#print axioms UPD.BG.sensorEquiv
#audit_axioms_strict UPD.BG.sensorEquiv
#print axioms UPD.BG.good_ofCfg_iff
#audit_axioms_strict UPD.BG.good_ofCfg_iff
#print axioms UPD.BG.inPair_of_ite_ne
#audit_axioms_strict UPD.BG.inPair_of_ite_ne
#print axioms UPD.BG.charge_eq
#audit_axioms_strict UPD.BG.charge_eq
#print axioms UPD.BG.charge_ofCfg
#audit_axioms_strict UPD.BG.charge_ofCfg
#print axioms UPD.BG.Wf_ofCfg
#audit_axioms_strict UPD.BG.Wf_ofCfg
#print axioms UPD.BG.Zf_eq_sensorSum
#audit_axioms_strict UPD.BG.Zf_eq_sensorSum
#print axioms UPD.BG.Zf_ready
#audit_axioms_strict UPD.BG.Zf_ready
#print axioms UPD.BG.Zf_ready_coupling
#audit_axioms_strict UPD.BG.Zf_ready_coupling
#print axioms UPD.BG.ZfHyp
#audit_axioms_strict UPD.BG.ZfHyp
#print axioms UPD.BG.Jc_bc_pos
#audit_axioms_strict UPD.BG.Jc_bc_pos
#print axioms UPD.BG.Ising.val_ne_zero
#audit_axioms_strict UPD.BG.Ising.val_ne_zero
#print axioms UPD.BG.rtail_root
#audit_axioms_strict UPD.BG.rtail_root
#print axioms UPD.BG.rtail_mem_nbr
#audit_axioms_strict UPD.BG.rtail_mem_nbr
#print axioms UPD.BG.redge_inj
#audit_axioms_strict UPD.BG.redge_inj
#print axioms UPD.BG.edgeC
#audit_axioms_strict UPD.BG.edgeC
#print axioms UPD.BG.edgeF
#audit_axioms_strict UPD.BG.edgeF
#print axioms UPD.BG.edgeC_pos
#audit_axioms_strict UPD.BG.edgeC_pos
#print axioms UPD.BG.edgeF_ne_zero
#audit_axioms_strict UPD.BG.edgeF_ne_zero
#print axioms UPD.BG.ready_of_edgeF_ne_zero
#audit_axioms_strict UPD.BG.ready_of_edgeF_ne_zero
#print axioms UPD.BG.Zf_eq
#audit_axioms_strict UPD.BG.Zf_eq
#print axioms UPD.BG.sum_edgeF
#audit_axioms_strict UPD.BG.sum_edgeF
#print axioms UPD.BG.recode_W
#audit_axioms_strict UPD.BG.recode_W
#print axioms UPD.BG.recode_kind
#audit_axioms_strict UPD.BG.recode_kind
#print axioms UPD.BG.measurable_unrelabel
#audit_axioms_strict UPD.BG.measurable_unrelabel
#print axioms UPD.BG.measurable_relabelC
#audit_axioms_strict UPD.BG.measurable_relabelC
#print axioms UPD.BG.map_unrelabel_map_relabelC
#audit_axioms_strict UPD.BG.map_unrelabel_map_relabelC
#print axioms UPD.BG.map_relabelC_map_unrelabel
#audit_axioms_strict UPD.BG.map_relabelC_map_unrelabel
#print axioms UPD.BG.liftCfg
#audit_axioms_strict UPD.BG.liftCfg
#print axioms UPD.BG.pay_effective
#audit_axioms_strict UPD.BG.pay_effective
#print axioms UPD.BG.map_spin_liftCfg
#audit_axioms_strict UPD.BG.map_spin_liftCfg
#print axioms UPD.BG.hEff_of
#audit_axioms_strict UPD.BG.hEff_of
#print axioms UPD.BG.hS_of
#audit_axioms_strict UPD.BG.hS_of
#print axioms UPD.BG.step1
#audit_axioms_strict UPD.BG.step1
#print axioms UPD.BG.Jc_antitone
#audit_axioms_strict UPD.BG.Jc_antitone
#print axioms UPD.BG.four_tanh_Jc_lt_one
#audit_axioms_strict UPD.BG.four_tanh_Jc_lt_one
#print axioms UPD.BG.windows_sep
#audit_axioms_strict UPD.BG.windows_sep
#print axioms UPD.BG.Gamma_J_le
#audit_axioms_strict UPD.BG.Gamma_J_le
#print axioms UPD.BG.Gamma_isDLR_unique
#audit_axioms_strict UPD.BG.Gamma_isDLR_unique
#print axioms UPD.BG.tiGibbs_unique
#audit_axioms_strict UPD.BG.tiGibbs_unique
#print axioms UPD.BG.bgMap_q
#audit_axioms_strict UPD.BG.bgMap_q
#print axioms UPD.BG.bgMap_injOn
#audit_axioms_strict UPD.BG.bgMap_injOn
#print axioms UPD.BG.shift_bgMap_ne
#audit_axioms_strict UPD.BG.shift_bgMap_ne
#print axioms UPD.BG.not_ti_of_ae_bg
#audit_axioms_strict UPD.BG.not_ti_of_ae_bg
#print axioms UPD.BG.haar_singleton
#audit_axioms_strict UPD.BG.haar_singleton
#print axioms UPD.BG.haar_noAtoms
#audit_axioms_strict UPD.BG.haar_noAtoms
#print axioms UPD.BG.not_countable_typical
#audit_axioms_strict UPD.BG.not_countable_typical
#print axioms UPD.BG.thm_main_moreover_of
#audit_axioms_strict UPD.BG.thm_main_moreover_of
#print axioms UPD.BG.exists_typical_phase
#audit_axioms_strict UPD.BG.exists_typical_phase
#print axioms UPD.BG.exists_tiGibbs_of
#audit_axioms_strict UPD.BG.exists_tiGibbs_of
#print axioms UPD.BG.thm_main_i_of
#audit_axioms_strict UPD.BG.thm_main_i_of
#print axioms UPD.BG.extLabel
#audit_axioms_strict UPD.BG.extLabel
#print axioms UPD.BG.measurable_extLabel
#audit_axioms_strict UPD.BG.measurable_extLabel
#print axioms UPD.BG.restr_extLabel
#audit_axioms_strict UPD.BG.restr_extLabel
#print axioms UPD.BG.compMeas
#audit_axioms_strict UPD.BG.compMeas
#print axioms UPD.BG.glueMeas
#audit_axioms_strict UPD.BG.glueMeas
#print axioms UPD.BG.map_restr_compMeas
#audit_axioms_strict UPD.BG.map_restr_compMeas
#print axioms UPD.BG.isProbabilityMeasure_compMeas
#audit_axioms_strict UPD.BG.isProbabilityMeasure_compMeas
#print axioms UPD.BG.isDLR_glueMeas
#audit_axioms_strict UPD.BG.isDLR_glueMeas
#print axioms UPD.BG.measurableSet_eval_eq
#audit_axioms_strict UPD.BG.measurableSet_eval_eq
#print axioms UPD.BG.glueMeas_real_eval
#audit_axioms_strict UPD.BG.glueMeas_real_eval
#print axioms UPD.BG.plusInd
#audit_axioms_strict UPD.BG.plusInd
#print axioms UPD.BG.abs_plusInd_le
#audit_axioms_strict UPD.BG.abs_plusInd_le
#print axioms UPD.BG.blockF
#audit_axioms_strict UPD.BG.blockF
#print axioms UPD.BG.blockF_local
#audit_axioms_strict UPD.BG.blockF_local
#print axioms UPD.BG.integral_plusInd_eval
#audit_axioms_strict UPD.BG.integral_plusInd_eval
#print axioms UPD.BG.measurable_spinField
#audit_axioms_strict UPD.BG.measurable_spinField
#print axioms UPD.BG.integral_blockF_shift
#audit_axioms_strict UPD.BG.integral_blockF_shift
#print axioms UPD.BG.le_boxAvg_sub
#audit_axioms_strict UPD.BG.le_boxAvg_sub
#print axioms UPD.BG.exists_rfree_near
#audit_axioms_strict UPD.BG.exists_rfree_near
#print axioms UPD.BG.exists_block_root
#audit_axioms_strict UPD.BG.exists_block_root
#print axioms UPD.BG.real_eval_of_ti
#audit_axioms_strict UPD.BG.real_eval_of_ti
#print axioms UPD.BG.exists_pm_Gamma
#audit_axioms_strict UPD.BG.exists_pm_Gamma
#print axioms UPD.BG.thm_main_ii_of
#audit_axioms_strict UPD.BG.thm_main_ii_of
#print axioms UPD.Compiler.OMachine
#audit_axioms_strict UPD.Compiler.OMachine
#print axioms UPD.Compiler.OMachine.Cfg
#audit_axioms_strict UPD.Compiler.OMachine.Cfg
#print axioms UPD.Compiler.OMachine.step
#audit_axioms_strict UPD.Compiler.OMachine.step
#print axioms UPD.Compiler.OMachine.start
#audit_axioms_strict UPD.Compiler.OMachine.start
#print axioms UPD.Compiler.OMachine.run
#audit_axioms_strict UPD.Compiler.OMachine.run
#print axioms UPD.Compiler.OMachine.HaltsOn
#audit_axioms_strict UPD.Compiler.OMachine.HaltsOn
#print axioms UPD.Compiler.OMachine.run_zero
#audit_axioms_strict UPD.Compiler.OMachine.run_zero
#print axioms UPD.Compiler.OMachine.run_succ
#audit_axioms_strict UPD.Compiler.OMachine.run_succ
#print axioms UPD.Compiler.OMachine.run_succ_of
#audit_axioms_strict UPD.Compiler.OMachine.run_succ_of
#print axioms UPD.Compiler.OMachine.step_right
#audit_axioms_strict UPD.Compiler.OMachine.step_right
#print axioms UPD.Compiler.OMachine.step_left
#audit_axioms_strict UPD.Compiler.OMachine.step_left
#print axioms UPD.Compiler.OMachine.card_states
#audit_axioms_strict UPD.Compiler.OMachine.card_states
#print axioms UPD.Compiler.OMachine.card_symbols
#audit_axioms_strict UPD.Compiler.OMachine.card_symbols
#print axioms UPD.Compiler.OMachine.stateEquiv
#audit_axioms_strict UPD.Compiler.OMachine.stateEquiv
#print axioms UPD.Compiler.OMachine.stateEquiv_init
#audit_axioms_strict UPD.Compiler.OMachine.stateEquiv_init
#print axioms UPD.Compiler.OMachine.stateEquiv_symm_zero
#audit_axioms_strict UPD.Compiler.OMachine.stateEquiv_symm_zero
#print axioms UPD.Compiler.OMachine.symEquiv0
#audit_axioms_strict UPD.Compiler.OMachine.symEquiv0
#print axioms UPD.Compiler.OMachine.symEquiv0_blank
#audit_axioms_strict UPD.Compiler.OMachine.symEquiv0_blank
#print axioms UPD.Compiler.OMachine.symEquiv
#audit_axioms_strict UPD.Compiler.OMachine.symEquiv
#print axioms UPD.Compiler.OMachine.symEquiv_one
#audit_axioms_strict UPD.Compiler.OMachine.symEquiv_one
#print axioms UPD.Compiler.OMachine.symEquiv_blank
#audit_axioms_strict UPD.Compiler.OMachine.symEquiv_blank
#print axioms UPD.Compiler.OMachine.toMachine
#audit_axioms_strict UPD.Compiler.OMachine.toMachine
#print axioms UPD.Compiler.OMachine.cfgMap
#audit_axioms_strict UPD.Compiler.OMachine.cfgMap
#print axioms UPD.Compiler.OMachine.halting_cfgMap
#audit_axioms_strict UPD.Compiler.OMachine.halting_cfgMap
#print axioms UPD.Compiler.OMachine.step_cfgMap
#audit_axioms_strict UPD.Compiler.OMachine.step_cfgMap
#print axioms UPD.Compiler.OMachine.start_cfgMap
#audit_axioms_strict UPD.Compiler.OMachine.start_cfgMap
#print axioms UPD.Compiler.OMachine.run_cfgMap
#audit_axioms_strict UPD.Compiler.OMachine.run_cfgMap
#print axioms UPD.Compiler.OMachine.toMachine_haltsOn
#audit_axioms_strict UPD.Compiler.OMachine.toMachine_haltsOn
#print axioms UPD.Compiler.FState
#audit_axioms_strict UPD.Compiler.FState
#print axioms UPD.Compiler.FState.equivOption
#audit_axioms_strict UPD.Compiler.FState.equivOption
#print axioms UPD.Compiler.FState.instFintype
#audit_axioms_strict UPD.Compiler.FState.instFintype
#print axioms UPD.Compiler.Fold.tget
#audit_axioms_strict UPD.Compiler.Fold.tget
#print axioms UPD.Compiler.Fold.tset
#audit_axioms_strict UPD.Compiler.Fold.tset
#print axioms UPD.Compiler.Fold.tset_mark
#audit_axioms_strict UPD.Compiler.Fold.tset_mark
#print axioms UPD.Compiler.Fold.tget_tset
#audit_axioms_strict UPD.Compiler.Fold.tget_tset
#print axioms UPD.Compiler.Fold.pos
#audit_axioms_strict UPD.Compiler.Fold.pos
#print axioms UPD.Compiler.Fold.pos_inj
#audit_axioms_strict UPD.Compiler.Fold.pos_inj
#print axioms UPD.Compiler.Fold.fmove
#audit_axioms_strict UPD.Compiler.Fold.fmove
#print axioms UPD.Compiler.Fold.isHalt
#audit_axioms_strict UPD.Compiler.Fold.isHalt
#print axioms UPD.Compiler.Fold.tr
#audit_axioms_strict UPD.Compiler.Fold.tr
#print axioms UPD.Compiler.fold
#audit_axioms_strict UPD.Compiler.fold
#print axioms UPD.Compiler.fold_init
#audit_axioms_strict UPD.Compiler.fold_init
#print axioms UPD.Compiler.fold_blank
#audit_axioms_strict UPD.Compiler.fold_blank
#print axioms UPD.Compiler.fold_one
#audit_axioms_strict UPD.Compiler.fold_one
#print axioms UPD.Compiler.fold_halting_init
#audit_axioms_strict UPD.Compiler.fold_halting_init
#print axioms UPD.Compiler.Fold.step_mk_right
#audit_axioms_strict UPD.Compiler.Fold.step_mk_right
#print axioms UPD.Compiler.Fold.step_mk_left
#audit_axioms_strict UPD.Compiler.Fold.step_mk_left
#print axioms UPD.Compiler.Fold.step_mk_right'
#audit_axioms_strict UPD.Compiler.Fold.step_mk_right'
#print axioms UPD.Compiler.Fold.step_mk_left'
#audit_axioms_strict UPD.Compiler.Fold.step_mk_left'
#print axioms UPD.Compiler.Fold.TapeRel
#audit_axioms_strict UPD.Compiler.Fold.TapeRel
#print axioms UPD.Compiler.Fold.Rel
#audit_axioms_strict UPD.Compiler.Fold.Rel
#print axioms UPD.Compiler.Fold.tapeRel_write
#audit_axioms_strict UPD.Compiler.Fold.tapeRel_write
#print axioms UPD.Compiler.Fold.tapeRel_right
#audit_axioms_strict UPD.Compiler.Fold.tapeRel_right
#print axioms UPD.Compiler.Fold.tapeRel_left
#audit_axioms_strict UPD.Compiler.Fold.tapeRel_left
#print axioms UPD.Compiler.Fold.rel_step_none
#audit_axioms_strict UPD.Compiler.Fold.rel_step_none
#print axioms UPD.Compiler.Fold.rel_step_some
#audit_axioms_strict UPD.Compiler.Fold.rel_step_some
#print axioms UPD.Compiler.Fold.mk₁_nth_nat
#audit_axioms_strict UPD.Compiler.Fold.mk₁_nth_nat
#print axioms UPD.Compiler.Fold.mk₁_nth_neg
#audit_axioms_strict UPD.Compiler.Fold.mk₁_nth_neg
#print axioms UPD.Compiler.Fold.getI_replicate
#audit_axioms_strict UPD.Compiler.Fold.getI_replicate
#print axioms UPD.Compiler.Fold.tape0
#audit_axioms_strict UPD.Compiler.Fold.tape0
#print axioms UPD.Compiler.Fold.tape1
#audit_axioms_strict UPD.Compiler.Fold.tape1
#print axioms UPD.Compiler.Fold.tapeRel_init
#audit_axioms_strict UPD.Compiler.Fold.tapeRel_init
#print axioms UPD.Compiler.Fold.run_two
#audit_axioms_strict UPD.Compiler.Fold.run_two
#print axioms UPD.Compiler.Fold.exists_rel
#audit_axioms_strict UPD.Compiler.Fold.exists_rel
#print axioms UPD.Compiler.Fold.sim_or_back
#audit_axioms_strict UPD.Compiler.Fold.sim_or_back
#print axioms UPD.Compiler.fold_haltsOn
#audit_axioms_strict UPD.Compiler.fold_haltsOn
#print axioms UPD.Compiler.Fold.Good
#audit_axioms_strict UPD.Compiler.Fold.Good
#print axioms UPD.Compiler.Fold.good_step
#audit_axioms_strict UPD.Compiler.Fold.good_step
#print axioms UPD.Compiler.Fold.run_succ_good
#audit_axioms_strict UPD.Compiler.Fold.run_succ_good
#print axioms UPD.Compiler.fold_run_isSome
#audit_axioms_strict UPD.Compiler.fold_run_isSome
#print axioms UPD.Compiler.bsucc
#audit_axioms_strict UPD.Compiler.bsucc
#print axioms UPD.Compiler.bin
#audit_axioms_strict UPD.Compiler.bin
#print axioms UPD.Compiler.pbits
#audit_axioms_strict UPD.Compiler.pbits
#print axioms UPD.Compiler.nbits
#audit_axioms_strict UPD.Compiler.nbits
#print axioms UPD.Compiler.pbits_succ
#audit_axioms_strict UPD.Compiler.pbits_succ
#print axioms UPD.Compiler.nbits_succ
#audit_axioms_strict UPD.Compiler.nbits_succ
#print axioms UPD.Compiler.bin_eq
#audit_axioms_strict UPD.Compiler.bin_eq
#print axioms UPD.Compiler.bsucc_eq
#audit_axioms_strict UPD.Compiler.bsucc_eq
#print axioms UPD.Compiler.primrec_bsucc
#audit_axioms_strict UPD.Compiler.primrec_bsucc
#print axioms UPD.Compiler.primrec_bin
#audit_axioms_strict UPD.Compiler.primrec_bin
#print axioms UPD.Compiler.ones
#audit_axioms_strict UPD.Compiler.ones
#print axioms UPD.Compiler.pbits_ones
#audit_axioms_strict UPD.Compiler.pbits_ones
#print axioms UPD.Compiler.bin_ones
#audit_axioms_strict UPD.Compiler.bin_ones
#print axioms UPD.Compiler.trPosNum_ones
#audit_axioms_strict UPD.Compiler.trPosNum_ones
#print axioms UPD.Compiler.trNat_ones
#audit_axioms_strict UPD.Compiler.trNat_ones
#print axioms UPD.Compiler.univFun
#audit_axioms_strict UPD.Compiler.univFun
#print axioms UPD.Compiler.univFun_partrec
#audit_axioms_strict UPD.Compiler.univFun_partrec
#print axioms UPD.Compiler.lenFun
#audit_axioms_strict UPD.Compiler.lenFun
#print axioms UPD.Compiler.lenFun_partrec
#audit_axioms_strict UPD.Compiler.lenFun_partrec
#print axioms UPD.Compiler.lenFun_ones
#audit_axioms_strict UPD.Compiler.lenFun_ones
#print axioms UPD.Compiler.exists_lenCode
#audit_axioms_strict UPD.Compiler.exists_lenCode
#print axioms UPD.Compiler.lenCode
#audit_axioms_strict UPD.Compiler.lenCode
#print axioms UPD.Compiler.lenCode_eval
#audit_axioms_strict UPD.Compiler.lenCode_eval
#print axioms UPD.Compiler.startInst
#audit_axioms_strict UPD.Compiler.startInst
#print axioms UPD.Compiler.fintypeK'
#audit_axioms_strict UPD.Compiler.fintypeK'
#print axioms UPD.Compiler.Γ₁
#audit_axioms_strict UPD.Compiler.Γ₁
#print axioms UPD.Compiler.Λ₁
#audit_axioms_strict UPD.Compiler.Λ₁
#print axioms UPD.Compiler.M₁
#audit_axioms_strict UPD.Compiler.M₁
#print axioms UPD.Compiler.M₀
#audit_axioms_strict UPD.Compiler.M₀
#print axioms UPD.Compiler.S₀
#audit_axioms_strict UPD.Compiler.S₀
#print axioms UPD.Compiler.supports₀
#audit_axioms_strict UPD.Compiler.supports₀
#print axioms UPD.Compiler.input
#audit_axioms_strict UPD.Compiler.input
#print axioms UPD.Compiler.init_eq
#audit_axioms_strict UPD.Compiler.init_eq
#print axioms UPD.Compiler.eval_dom
#audit_axioms_strict UPD.Compiler.eval_dom
#print axioms UPD.Compiler.Q₀
#audit_axioms_strict UPD.Compiler.Q₀
#print axioms UPD.Compiler.instInhabitedQ₀
#audit_axioms_strict UPD.Compiler.instInhabitedQ₀
#print axioms UPD.Compiler.toQ
#audit_axioms_strict UPD.Compiler.toQ
#print axioms UPD.Compiler.toQ_val
#audit_axioms_strict UPD.Compiler.toQ_val
#print axioms UPD.Compiler.M₀'
#audit_axioms_strict UPD.Compiler.M₀'
#print axioms UPD.Compiler.liftC
#audit_axioms_strict UPD.Compiler.liftC
#print axioms UPD.Compiler.step_liftC
#audit_axioms_strict UPD.Compiler.step_liftC
#print axioms UPD.Compiler.respects_liftC
#audit_axioms_strict UPD.Compiler.respects_liftC
#print axioms UPD.Compiler.eval_restrict
#audit_axioms_strict UPD.Compiler.eval_restrict
#print axioms UPD.Compiler.a0
#audit_axioms_strict UPD.Compiler.a0
#print axioms UPD.Compiler.a1
#audit_axioms_strict UPD.Compiler.a1
#print axioms UPD.Compiler.input_ones
#audit_axioms_strict UPD.Compiler.input_ones
#print axioms UPD.Compiler.a1_ne
#audit_axioms_strict UPD.Compiler.a1_ne
#print axioms UPD.Compiler.UF
#audit_axioms_strict UPD.Compiler.UF
#print axioms UPD.Compiler.UF_ne
#audit_axioms_strict UPD.Compiler.UF_ne
#print axioms UPD.Compiler.univMachine
#audit_axioms_strict UPD.Compiler.univMachine
#print axioms UPD.Compiler.univMachine_haltsOn
#audit_axioms_strict UPD.Compiler.univMachine_haltsOn
#print axioms UPD.Compiler.univMachine_run_isSome
#audit_axioms_strict UPD.Compiler.univMachine_run_isSome
#print axioms UPD.Compiler.univMachine_universal
#audit_axioms_strict UPD.Compiler.univMachine_universal

/-! Complete imported-project audit, including generated and private declarations. -/
set_option maxHeartbeats 20000000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx]!
      if mod.toString.startsWith "UndecidablePhaseDiagram" then
        if ci matches .axiomInfo _ then throwError "Project axiom declaration {n}"
        let ax := (← Lean.collectAxioms n).toList
        for a in ax do
          unless standard.contains a do throwError "Unexpected axiom {a} in {n}"
        logInfo m!"UPD_DECL:{toJson (n.toString, mod.toString, ax.map Name.toString) |>.compress}"
        count := count + 1
  let check (n : Name) (t : Expr) : CommandElabM Unit := do
    let some ci := env.find? n | throwError "Missing {n}"
    unless ci matches .thmInfo _ do throwError "{n} is not a theorem"
    unless ci.type == t do throwError "{n} statement changed"
  check ``UPD.theorem_A (mkForall `h1 .default (mkConst ``UPD.H1)
    (mkForall `h2 .default (mkConst ``UPD.H2) (mkConst ``UPD.TheoremA)))
  check ``UPD.corollary_B (mkForall `h1 .default (mkConst ``UPD.H1)
    (mkForall `h2 .default (mkConst ``UPD.H2) (mkConst ``UPD.CorollaryB)))
  check ``UPD.existsUniversal (mkConst ``UPD.ExistsUniversal)
  logInfo m!"UPD_FINAL_TYPES_OK"
  logInfo m!"UPD_DECL_COUNT:{count}"
