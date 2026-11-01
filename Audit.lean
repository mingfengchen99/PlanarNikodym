import PlanarNikodym
import Lean.Util.CollectAxioms

/-! This file is checked by scripts/check.sh. It fails if any project declaration
has a transitive axiom beyond Lean's three standard logical axioms. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "PlanarNikodym." then
      count := count + 1
      match info with
      | .axiomInfo _ => throwError "Project axiom: {name}"
      | .thmInfo _ => theoremCount := theoremCount + 1
      | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
  logInfo m!"Audited {count} project declarations ({theoremCount} theorems): only propext, Classical.choice, Quot.sound allowed."


-- Audit by defining module as well as public namespace, including private helpers.
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let isProjectModule := fun n : Name =>
    n == `PlanarNikodym || n.toString.startsWith "PlanarNikodym."
  let moduleCount := (modules.toList.filter isProjectModule).length
  let mut total : Nat := 0
  let mut theorems : Nat := 0
  let mut outside : Nat := 0
  let mut outsideTheorems : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless isProjectModule modules[idx.toNat]! do continue
    total := total + 1
    if let .thmInfo _ := info then theorems := theorems + 1
    if let .axiomInfo _ := info then throwError "Project module axiom: {name}"
    if info.isUnsafe then throwError "Unsafe project module declaration: {name}"
    unless name.toString.startsWith "PlanarNikodym." do
      outside := outside + 1
      if let .thmInfo _ := info then outsideTheorems := outsideTheorems + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do throwError "Unapproved axiom {ax} in {name}"
  logInfo m!"Module origin audit: {total} declarations ({theorems} theorems); {outside} outside namespace ({outsideTheorems} theorems); {moduleCount} project modules. No project axioms or unsafe declarations."

-- Explicit public result checks retained after maximal-route retirement.
#check PlanarNikodym.lemma_5_6_interval
#check PlanarNikodym.analyticSet_nullMeasurableSet
#check PlanarNikodym.exists_separated_scalarGradientSlope_patches
#check PlanarNikodym.lintegral_volume_scalarProjections_pos
#check PlanarNikodym.ProjectionModel.exists_null_set_or_separated_twoSlice_points
#check PlanarNikodym.ProjectionModel.exists_null_set_of_twoSlice_projected_sweeps
#check PlanarNikodym.ProjectionModel.exists_null_set_of_twoSlice_projection_integrals
#print axioms PlanarNikodym.analyticSet_nullMeasurableSet
#print axioms PlanarNikodym.exists_separated_scalarGradientSlope_patches
#print axioms PlanarNikodym.ProjectionModel.exists_null_set_or_separated_twoSlice_points
#print axioms PlanarNikodym.ProjectionModel.exists_null_set_of_twoSlice_projected_sweeps
#print axioms PlanarNikodym.ProjectionModel.exists_null_set_of_twoSlice_projection_integrals
#check PlanarNikodym.polynomial_eq_zero_of_two_taylor_jets
#check PlanarNikodym.exists_uniform_glyzMixedMoment_perturbation
#check PlanarNikodym.linearIndependent_glyzProjectedMomentJets
#check PlanarNikodym.integral_glyzMomentWeight_convolution_le
#check PlanarNikodym.integral_glyzMomentWeight_tail_le
#check PlanarNikodym.glyz_degree_one_eLpNorm_sq
#print axioms PlanarNikodym.exists_uniform_glyzMixedMoment_perturbation
#print axioms PlanarNikodym.linearIndependent_glyzProjectedMomentJets
#print axioms PlanarNikodym.integral_glyzMomentWeight_convolution_le
#print axioms PlanarNikodym.integral_glyzMomentWeight_tail_le
#print axioms PlanarNikodym.glyz_degree_one_eLpNorm_sq
set_option pp.proofs false in
#print PlanarNikodym.lemma_5_6_interval
#print axioms PlanarNikodym.lemma_5_6_interval
#print axioms PlanarNikodym.exists_eval_det_ne_zero
#print axioms PlanarNikodym.Family.smooth_graph_positive_iff
#print axioms PlanarNikodym.Family.admitsNikodym_iff_byTimes
#print axioms PlanarNikodym.Family.pointRank_le_aux
#print axioms PlanarNikodym.Family.curveRank_le_pointRank_add_two
#print axioms PlanarNikodym.Examples.horizontal_ranks
#print axioms PlanarNikodym.Examples.sliding_ranks
#print axioms PlanarNikodym.Examples.lines_ranks
#print axioms PlanarNikodym.Examples.polynomial_rank
#print axioms PlanarNikodym.Examples.empty_evaluation
#check PlanarNikodym.lemma_6_1_interval
#check PlanarNikodym.corollary_6_2
#check PlanarNikodym.corollary_6_3
set_option pp.proofs false in
#print PlanarNikodym.lemma_6_1_interval
set_option pp.proofs false in
#print PlanarNikodym.corollary_6_2
set_option pp.proofs false in
#print PlanarNikodym.corollary_6_3
#print axioms PlanarNikodym.lemma_6_1
#print axioms PlanarNikodym.lemma_6_1_interval
#print axioms PlanarNikodym.corollary_6_2
#print axioms PlanarNikodym.corollary_6_3
#print axioms PlanarNikodym.corollary_6_3_functions
#print axioms PlanarNikodym.Examples.constantFamily_reduction
#print axioms PlanarNikodym.Examples.lines_center_reduction
#check PlanarNikodym.lemma_7_1
#check PlanarNikodym.theorem_1_5_case_equal
#check PlanarNikodym.theorem_1_5_case_rank_one
set_option pp.proofs false in
#print PlanarNikodym.lemma_7_1
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_5_case_equal
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_5_case_rank_one
#print axioms PlanarNikodym.lemma_7_1
#print axioms PlanarNikodym.lemma_7_1_finite_exceptions
#print axioms PlanarNikodym.theorem_1_5_case_equal
#print axioms PlanarNikodym.theorem_1_5_case_rank_one
#print axioms PlanarNikodym.one_parameter_graph_preimage_null
#print axioms PlanarNikodym.rank_one_global
#print axioms PlanarNikodym.Examples.sliding_classification
#print axioms PlanarNikodym.Examples.zero_rank_classification
#print axioms PlanarNikodym.Examples.horizontal_classification
#print axioms PlanarNikodym.Examples.horizontalWithAux_classification
#check PlanarNikodym.maximal_gap_centers_countable
#check PlanarNikodym.maximal_gap_not_reused
#check PlanarNikodym.intermediate_locallyReused
#check PlanarNikodym.exists_intermediate_model
#check PlanarNikodym.theorem_1_5_case_maximal_gap
#check PlanarNikodym.theorem_1_5_case_positive_intermediate
#check PlanarNikodym.theorem_1_5_conditional
set_option pp.proofs false in
#print PlanarNikodym.BocherInput
set_option pp.proofs false in
#print PlanarNikodym.CinematicNullInput
set_option pp.proofs false in
#print PlanarNikodym.ProjectionConstructionInput
set_option pp.proofs false in
#print PlanarNikodym.ProjectionAvoidanceInput
set_option pp.proofs false in
#print PlanarNikodym.P5Inputs
set_option pp.proofs false in
#print PlanarNikodym.ProjectionModel
set_option pp.proofs false in
#print PlanarNikodym.ConstantRankConclusions
set_option pp.proofs false in
#print PlanarNikodym.Theorem15Statement
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_5_conditional
#print axioms PlanarNikodym.maximal_gap_centers_countable
#print axioms PlanarNikodym.maximal_gap_not_reused
#print axioms PlanarNikodym.intermediate_locallyReused
#print axioms PlanarNikodym.exists_intermediate_model
#print axioms PlanarNikodym.full_curve_rank_cinematic_exceptions_finite
#print axioms PlanarNikodym.time_incidence_null_of_regular_patches
#print axioms PlanarNikodym.theorem_1_5_case_maximal_gap
#print axioms PlanarNikodym.theorem_1_5_case_positive_intermediate
#print axioms PlanarNikodym.theorem_1_5_conditional
#print axioms PlanarNikodym.Examples.affineGraphs_no_reuse
#print axioms PlanarNikodym.Examples.lines_locallyReused
#print axioms PlanarNikodym.Examples.horizontal_projection_model
#print axioms PlanarNikodym.Examples.bounded_lines_classification
#check PlanarNikodym.lemma_5_7_conditional
#check PlanarNikodym.RankCellStep.flatten
#check PlanarNikodym.RankDecomposition.proposition_1_6_of_decomposition
#check PlanarNikodym.proposition_1_6_conditional
#check PlanarNikodym.exists_ball_parameter_cover
#check PlanarNikodym.BallParameterCover.localization_conditional
#check PlanarNikodym.general_classification_of_analytic
#check PlanarNikodym.theorem_1_4_conditional
set_option pp.proofs false in
#print PlanarNikodym.AnalyticPiece
set_option pp.proofs false in
#print PlanarNikodym.RankPiece
set_option pp.proofs false in
#print PlanarNikodym.RankDecomposition
set_option pp.proofs false in
#print PlanarNikodym.RankCellStep
set_option pp.proofs false in
#print PlanarNikodym.TameGeometryInput
set_option pp.proofs false in
#print PlanarNikodym.P6Inputs
set_option pp.proofs false in
#print PlanarNikodym.RankDecomposition.Proposition16Conclusions
set_option pp.proofs false in
#print PlanarNikodym.Proposition16Statement
set_option pp.proofs false in
#print PlanarNikodym.Theorem14Statement
set_option pp.proofs false in
#print PlanarNikodym.proposition_1_6_conditional
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_4_conditional
#print axioms PlanarNikodym.HasPositivePart.exists_of_countable_cover
#print axioms PlanarNikodym.HasPositivePart.exists_of_countable_nullMeasurable_cover
#print axioms PlanarNikodym.AnalyticPiece.comp
#print axioms PlanarNikodym.AnalyticPiece.locallyReused
#print axioms PlanarNikodym.RankCellStep.flatten
#print axioms PlanarNikodym.lemma_5_7_conditional
#print axioms PlanarNikodym.RankDecomposition.remainder_centers_closure_null
#print axioms PlanarNikodym.RankDecomposition.proposition_1_6_of_decomposition
#print axioms PlanarNikodym.proposition_1_6_conditional
#print axioms PlanarNikodym.OpenParameterCover.locallyReusedCovered
#print axioms PlanarNikodym.BallParameterCover.localization_conditional
#print axioms PlanarNikodym.general_classification_of_analytic
#print axioms PlanarNikodym.theorem_1_4_conditional
#print axioms PlanarNikodym.Examples.horizontalSplit_proposition16
#print axioms PlanarNikodym.Examples.horizontalSplit_exceptional_partition
#print axioms PlanarNikodym.Examples.empty_domain_general_classification
#check PlanarNikodym.theorem_2_1_of_jet_smoothing
#check PlanarNikodym.corollary_2_2_of_inputs
#check PlanarNikodym.dyadic_majorant_estimate
#check PlanarNikodym.AnalyticMaximalPackage.open_maximal_estimate
#check PlanarNikodym.Family.OpenMaximalEstimate.incidence_null
#check PlanarNikodym.cinematicNullInput_of_analysis
#check PlanarNikodym.corollary_1_2_conditional
#check PlanarNikodym.theorem_1_5_from_analysis
#check PlanarNikodym.theorem_1_4_from_analysis
set_option pp.proofs false in
#print PlanarNikodym.FrequencyCutoff
set_option pp.proofs false in
#print PlanarNikodym.JetSmoothingInput
set_option pp.proofs false in
#print PlanarNikodym.BandSobolevInput
set_option pp.proofs false in
#print PlanarNikodym.LowFrequencyInput
set_option pp.proofs false in
#print PlanarNikodym.OpenReconstructionInput
set_option pp.proofs false in
#print PlanarNikodym.AnalyticMaximalPackage
set_option pp.proofs false in
#print PlanarNikodym.CinematicAnalysisInput
set_option pp.proofs false in
#print PlanarNikodym.P7Inputs
set_option pp.proofs false in
#print PlanarNikodym.cinematicNullInput_of_analysis
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_4_from_analysis
#print axioms PlanarNikodym.standardFrequencyCutoff
#print axioms PlanarNikodym.FrequencyCutoff.finite_partition
#print axioms PlanarNikodym.FrequencyCutoff.bandSymbol_vanishes_below_scale
#print axioms PlanarNikodym.eLpNorm_iSup_nonnegative
#print axioms PlanarNikodym.eLpNorm_tsum_nonnegative_le
#print axioms PlanarNikodym.dyadic_majorant_estimate
#print axioms PlanarNikodym.theorem_2_1_of_jet_smoothing
#print axioms PlanarNikodym.corollary_2_2_of_inputs
#print axioms PlanarNikodym.AnalyticMaximalPackage.open_maximal_estimate
#print axioms PlanarNikodym.outer_null_of_open_tests
#print axioms PlanarNikodym.Family.OpenMaximalEstimate.incidence_null
#print axioms PlanarNikodym.cinematicNullInput_of_analysis
#print axioms PlanarNikodym.corollary_1_2_conditional
#print axioms PlanarNikodym.theorem_1_5_from_analysis
#print axioms PlanarNikodym.theorem_1_4_from_analysis
#print axioms PlanarNikodym.Examples.null_indicator_positive_on_its_curve
#check PlanarNikodym.bocher_input
#check PlanarNikodym.theorem_5_3
#check PlanarNikodym.generic_analytic_function_rank
#check PlanarNikodym.rank_drop_analytic_dichotomy
#check PlanarNikodym.generic_double_rank
#check PlanarNikodym.Family.centers_isSigmaCompact
#check PlanarNikodym.Family.centers_measurable_of_analytic
#check PlanarNikodym.full_curve_rank_cinematic_exceptions_finite_proved
#check PlanarNikodym.lemma_5_7_after_center_measurability
#check PlanarNikodym.theorem_1_5_after_bocher
#check PlanarNikodym.theorem_1_4_after_foundations
set_option pp.proofs false in
#print PlanarNikodym.bocher_input
set_option pp.proofs false in
#print PlanarNikodym.theorem_5_3
set_option pp.proofs false in
#print PlanarNikodym.generic_double_rank
set_option pp.proofs false in
#print PlanarNikodym.Family.centers_isSigmaCompact
set_option pp.proofs false in
#print PlanarNikodym.P8RemainingInputs
set_option pp.proofs false in
#print PlanarNikodym.TameCellInput
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_4_after_foundations
#print axioms PlanarNikodym.bocher_interior
#print axioms PlanarNikodym.bocher_input
#print axioms PlanarNikodym.theorem_5_3
#print axioms PlanarNikodym.generic_analytic_function_rank
#print axioms PlanarNikodym.rank_drop_analytic_dichotomy
#print axioms PlanarNikodym.generic_double_rank
#print axioms PlanarNikodym.Family.centers_isSigmaCompact
#print axioms PlanarNikodym.Family.centers_measurable_of_analytic
#print axioms PlanarNikodym.TameCellInput.toTameGeometry
#print axioms PlanarNikodym.full_curve_rank_cinematic_exceptions_finite_proved
#print axioms PlanarNikodym.theorem_1_4_after_foundations
#print axioms PlanarNikodym.Examples.sin_cos_independent
#print axioms PlanarNikodym.Examples.quadratic_pair_has_one_exception
#print axioms PlanarNikodym.Examples.affineGraphs_no_nikodym_after_bocher
#check PlanarNikodym.vertical_derivative_surjective
#check PlanarNikodym.Family.ranks_of_parameter_change
#check PlanarNikodym.AnalyticPiece.ranks_eq_of_surjective
#check PlanarNikodym.generic_rank_evaluation_minor
#check PlanarNikodym.generic_double_rank_minor
#check PlanarNikodym.finiteComponentCover
#check PlanarNikodym.RegularCellCover.toRankCellStep
#check PlanarNikodym.AnalyticCellCover.flattenRankSteps
#check PlanarNikodym.lemma_5_7_from_compatible_cells
#check PlanarNikodym.theorem_1_4_from_compatible_cells
set_option pp.proofs false in
#print PlanarNikodym.Family.ranks_of_parameter_change
set_option pp.proofs false in
#print PlanarNikodym.EvaluationMinor
set_option pp.proofs false in
#print PlanarNikodym.generic_double_rank_minor
set_option pp.proofs false in
#print PlanarNikodym.RegularCellCover
set_option pp.proofs false in
#print PlanarNikodym.AnalyticCellInput
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_4_from_compatible_cells
#print axioms PlanarNikodym.vertical_derivative_surjective
#print axioms PlanarNikodym.Family.ranks_of_parameter_change
#print axioms PlanarNikodym.generic_rank_evaluation_minor
#print axioms PlanarNikodym.generic_double_rank_minor
#print axioms PlanarNikodym.finiteComponentCover
#print axioms PlanarNikodym.RegularCellCover.toRankCellStep
#print axioms PlanarNikodym.AnalyticCellCover.flattenRankSteps
#print axioms PlanarNikodym.AnalyticCellInput.toTameCell
#print axioms PlanarNikodym.lemma_5_7_from_compatible_cells
#print axioms PlanarNikodym.theorem_1_4_from_compatible_cells
#check PlanarNikodym.Examples.quadraticSlide_regular_ranks
#check PlanarNikodym.Examples.quadraticZeroPiece_center_image
#check PlanarNikodym.Examples.quadraticZeroPiece_centers_positive
#check PlanarNikodym.Examples.quadraticDecomposition
#check PlanarNikodym.Examples.quadraticDecomposition_exception_empty
#check PlanarNikodym.Examples.quadraticDecomposition_partition
#check PlanarNikodym.Examples.quadraticSlide_admitsNikodym
#print axioms PlanarNikodym.Examples.quadraticDecomposition
#print axioms PlanarNikodym.Examples.quadraticDecomposition_partition
#print axioms PlanarNikodym.Examples.quadraticSlide_admitsNikodym
#print axioms PlanarNikodym.Examples.quadraticZeroPiece_centers_positive
#check PlanarNikodym.lemma_5_7_connected_cells
#check PlanarNikodym.BallParameterCover.localization_of_decompositions
#check PlanarNikodym.general_classification_from_connected_cells
#check PlanarNikodym.theorem_1_4_from_connected_cells
set_option pp.proofs false in
#print PlanarNikodym.ConnectedCellInput
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_4_from_connected_cells
#print axioms PlanarNikodym.AnalyticCellInput.toConnected
#print axioms PlanarNikodym.lemma_5_7_connected_cells
#print axioms PlanarNikodym.BallParameterCover.localization_of_decompositions
#print axioms PlanarNikodym.theorem_1_4_from_connected_cells
#check PlanarNikodym.inverseFourierIntegral_integrable
#check PlanarNikodym.inverseFourierIntegral_dilate
#check PlanarNikodym.integral_inverseFourierIntegral
#check PlanarNikodym.FrequencyCutoff.low_continuous
#check PlanarNikodym.lowFrequencyInput_of_compactCutoff
set_option pp.proofs false in
#print PlanarNikodym.lowFrequencyInput_of_compactCutoff
#print axioms PlanarNikodym.inverseFourierIntegral_integrable
#print axioms PlanarNikodym.integral_inverseFourierIntegral
#print axioms PlanarNikodym.lowFrequencyInput_of_compactCutoff
#check PlanarNikodym.eLpNorm_iSup_enorm_le_dyadic_eLpNorm_add_deriv
#check PlanarNikodym.Family.bandSobolevInput_aux_zero
#check PlanarNikodym.Family.bandSobolevInput_aux_one_of_contDiff_bands
set_option pp.proofs false in
#print PlanarNikodym.Family.bandSobolevInput_aux_one_of_contDiff_bands
#print axioms PlanarNikodym.Family.bandSobolevInput_aux_zero
#print axioms PlanarNikodym.Family.bandSobolevInput_aux_one_of_contDiff_bands
#check PlanarNikodym.ProjectionModel.timeJet_fderiv_matrix
#check PlanarNikodym.ProjectionModel.timeJet_fderiv_injective_ae
#check PlanarNikodym.ProjectionModel.measurableSet_not_timeCovered
#check PlanarNikodym.ProjectionModel.exists_tangencyTimes_pos_of_timeCovered
set_option pp.proofs false in
#print PlanarNikodym.ProjectionModel.timeJet_fderiv_injective_ae
#print axioms PlanarNikodym.ProjectionModel.timeJet_fderiv_injective_ae
#print axioms PlanarNikodym.ProjectionModel.variationJetDegenerateSet_null
#print axioms PlanarNikodym.ProjectionModel.measurableSet_not_timeCovered
#check PlanarNikodym.exists_openSmoothApproximation
#check PlanarNikodym.Family.positiveMaximal_open_eq_iSup_smooth
#check PlanarNikodym.Family.openMaximalEstimate_of_smooth_tests
set_option pp.proofs false in
#print PlanarNikodym.Family.openMaximalEstimate_of_smooth_tests
#print axioms PlanarNikodym.exists_openSmoothApproximation
#print axioms PlanarNikodym.Family.positiveMaximal_open_eq_iSup_smooth
#print axioms PlanarNikodym.Family.openMaximalEstimate_of_smooth_tests
#check PlanarNikodym.FrequencyCutoff.lowAtScale_tendsto
#check PlanarNikodym.FrequencyCutoff.finite_reconstruction
#check PlanarNikodym.Family.cutoffAverage_reconstruction_majorant
#check PlanarNikodym.Family.measurable_positiveMaximal
#check PlanarNikodym.Family.positiveMaximal_le_cutoffMaximal
#check PlanarNikodym.Family.openMaximalEstimate_of_dyadic_decay
#check PlanarNikodym.Family.exists_analytic_cutoff_neighborhood
#check PlanarNikodym.Family.exists_cinematic_cutoff_neighborhood
set_option pp.proofs false in
#print PlanarNikodym.SmoothMaximalPackage
set_option pp.proofs false in
#print PlanarNikodym.Family.openMaximalEstimate_of_dyadic_decay
#print axioms PlanarNikodym.FrequencyCutoff.lowAtScale_tendsto
#print axioms PlanarNikodym.Family.cutoffAverage_reconstruction_majorant
#print axioms PlanarNikodym.Family.openMaximalEstimate_of_dyadic_decay
#print axioms PlanarNikodym.Family.exists_analytic_cutoff_neighborhood
#print axioms PlanarNikodym.Family.exists_cinematic_cutoff_neighborhood
#check PlanarNikodym.FrequencyCutoff.band_contDiff_one
#check PlanarNikodym.Family.bandAverage_contDiff_one
#check PlanarNikodym.Family.bandSobolevInput_aux_one
#check PlanarNikodym.iSup_enorm_le_scaled_eLpNorm_two_of_contDiff
set_option pp.proofs false in
#print PlanarNikodym.Family.bandSobolevInput_aux_one
#print axioms PlanarNikodym.Family.bandSobolevInput_aux_one
#print axioms PlanarNikodym.iSup_enorm_le_scaled_eLpNorm_two_of_contDiff
#check PlanarNikodym.regular_zero_set_null
#check PlanarNikodym.ProjectionModel.timeCovered_parameters_null
#check PlanarNikodym.ProjectionModel.centerTrace_hasPositivePart_of_conull
#check PlanarNikodym.projection_avoidance_input
#check PlanarNikodym.positive_intermediate_localReuseNotCovered_proved
set_option pp.proofs false in
#print PlanarNikodym.projection_avoidance_input
#print axioms PlanarNikodym.regular_zero_set_null
#print axioms PlanarNikodym.ProjectionModel.timeCovered_parameters_null
#print axioms PlanarNikodym.ProjectionModel.centerTrace_hasPositivePart_of_conull
#print axioms PlanarNikodym.projection_avoidance_input
#print axioms PlanarNikodym.positive_intermediate_localReuseNotCovered_proved
#check PlanarNikodym.smoothMaximalPackage_aux_one
#check PlanarNikodym.cinematicNullInput_of_smooth_analysis
#check PlanarNikodym.theorem_1_5_after_avoidance
#check PlanarNikodym.theorem_1_4_after_avoidance
#check PlanarNikodym.proposition_1_6_after_avoidance
set_option pp.proofs false in
#print PlanarNikodym.CinematicSmoothAnalysisInput
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_5_after_avoidance
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_4_after_avoidance
#print axioms PlanarNikodym.smoothMaximalPackage_aux_one
#print axioms PlanarNikodym.theorem_1_5_after_avoidance
#print axioms PlanarNikodym.theorem_1_4_after_avoidance
#print axioms PlanarNikodym.proposition_1_6_after_avoidance
#check PlanarNikodym.eLpNorm_iSup_aux_two_le_scaled_fullJet
#check PlanarNikodym.Family.cutoffMaximal_le_scaledJetNorm_aux_two_of_contDiff
#check PlanarNikodym.Family.bandSobolevInput_aux_two_of_contDiff_bands
set_option pp.proofs false in
#print PlanarNikodym.Family.bandSobolevInput_aux_two_of_contDiff_bands
#print axioms PlanarNikodym.eLpNorm_iSup_aux_two_le_scaled_fullJet
#print axioms PlanarNikodym.Family.cutoffMaximal_le_scaledJetNorm_aux_two_of_contDiff
#print axioms PlanarNikodym.Family.bandSobolevInput_aux_two_of_contDiff_bands
#check PlanarNikodym.hasFDerivAt_convolution_schwartz
#check PlanarNikodym.contDiff_nat_convolution_schwartz
#check PlanarNikodym.contDiff_infty_convolution_schwartz
#check PlanarNikodym.FrequencyCutoff.band_contDiff_infty
#check PlanarNikodym.FrequencyCutoff.low_contDiff_infty
#check PlanarNikodym.Family.cutoffAverage_contDiff
#check PlanarNikodym.Family.bandAverage_contDiff
#check PlanarNikodym.Family.bandSobolevInput_aux_two
#check PlanarNikodym.smoothMaximalPackage_aux_two
#check PlanarNikodym.Family.openMaximalEstimate_aux_two_of_jet_smoothing
#check PlanarNikodym.Family.exists_cinematic_sobolev_cutoff_aux_two
set_option pp.proofs false in
#print PlanarNikodym.FrequencyCutoff.band_contDiff_infty
set_option pp.proofs false in
#print PlanarNikodym.Family.bandSobolevInput_aux_two
set_option pp.proofs false in
#print PlanarNikodym.smoothMaximalPackage_aux_two
set_option pp.proofs false in
#print PlanarNikodym.Family.openMaximalEstimate_aux_two_of_jet_smoothing
set_option pp.proofs false in
#print PlanarNikodym.Family.exists_cinematic_sobolev_cutoff_aux_two
#print axioms PlanarNikodym.hasFDerivAt_convolution_schwartz
#print axioms PlanarNikodym.contDiff_infty_convolution_schwartz
#print axioms PlanarNikodym.FrequencyCutoff.band_contDiff_infty
#print axioms PlanarNikodym.FrequencyCutoff.low_contDiff_infty
#print axioms PlanarNikodym.Family.bandAverage_contDiff
#print axioms PlanarNikodym.Family.bandSobolevInput_aux_two
#print axioms PlanarNikodym.smoothMaximalPackage_aux_two
#print axioms PlanarNikodym.Family.openMaximalEstimate_aux_two_of_jet_smoothing
#print axioms PlanarNikodym.Family.exists_cinematic_sobolev_cutoff_aux_two
#check PlanarNikodym.auxConsLinear_measurePreserving
#check PlanarNikodym.norm_iteratedFDeriv_cons_slice_le
#check PlanarNikodym.norm_iteratedFDeriv_auxHeadDerivative_le
#check PlanarNikodym.enorm_le_scaled_fullJet_aux
#check PlanarNikodym.iSup_enorm_aux_le_scaled_fullJet
#check PlanarNikodym.continuous_auxiliary_iteratedFDeriv_of_smooth
#check PlanarNikodym.eLpNorm_iSup_aux_le_scaled_fullJet
#check PlanarNikodym.Family.cutoffMaximal_le_scaledJetNorm_of_smooth
#check PlanarNikodym.Family.bandSobolevInput_aux
#check PlanarNikodym.Family.bandSobolevInput_aux_of_order_ge
#check PlanarNikodym.smoothMaximalPackage_aux
#check PlanarNikodym.Family.openMaximalEstimate_of_jet_smoothing
#check PlanarNikodym.Family.exists_cinematic_sobolev_cutoff
set_option pp.proofs false in
#print PlanarNikodym.iSup_enorm_aux_le_scaled_fullJet
set_option pp.proofs false in
#print PlanarNikodym.Family.bandSobolevInput_aux
set_option pp.proofs false in
#print PlanarNikodym.Family.bandSobolevInput_aux_of_order_ge
set_option pp.proofs false in
#print PlanarNikodym.smoothMaximalPackage_aux
set_option pp.proofs false in
#print PlanarNikodym.Family.openMaximalEstimate_of_jet_smoothing
set_option pp.proofs false in
#print PlanarNikodym.Family.exists_cinematic_sobolev_cutoff
#print axioms PlanarNikodym.auxConsLinear_measurePreserving
#print axioms PlanarNikodym.norm_iteratedFDeriv_cons_slice_le
#print axioms PlanarNikodym.enorm_le_scaled_fullJet_aux
#print axioms PlanarNikodym.iSup_enorm_aux_le_scaled_fullJet
#print axioms PlanarNikodym.continuous_auxiliary_iteratedFDeriv_of_smooth
#print axioms PlanarNikodym.eLpNorm_iSup_aux_le_scaled_fullJet
#print axioms PlanarNikodym.Family.cutoffMaximal_le_scaledJetNorm_of_smooth
#print axioms PlanarNikodym.Family.bandSobolevInput_aux
#print axioms PlanarNikodym.Family.bandSobolevInput_aux_of_order_ge
#print axioms PlanarNikodym.smoothMaximalPackage_aux
#print axioms PlanarNikodym.Family.openMaximalEstimate_of_jet_smoothing
#print axioms PlanarNikodym.Family.exists_cinematic_sobolev_cutoff
#check PlanarNikodym.exists_finite_cutoff_partition
#check PlanarNikodym.Family.cutoffAverage_sum_cutoff
#check PlanarNikodym.Family.auxiliaryJetNorm_sum_cutoff_le
#check PlanarNikodym.Family.scaledJetNorm_sum_cutoff_le
#check PlanarNikodym.jetSmoothingInput_sum_cutoff
#check PlanarNikodym.jetSmoothingInput_of_local_cutoffs
#check PlanarNikodym.hasFDerivAt_integral_of_compact_time_support
#check PlanarNikodym.Family.fderiv_cutoffIntegrand_apply
#check PlanarNikodym.Family.fderiv_cutoffAverage_eq_integral
#check PlanarNikodym.Family.fderiv_cutoffAverage_apply
#check PlanarNikodym.Family.fderiv_bandAverage_apply
set_option pp.proofs false in
#print PlanarNikodym.PointwiseJetSmoothingInput
set_option pp.proofs false in
#print PlanarNikodym.cinematicSmoothAnalysisInput_of_pointwise_jet_smoothing
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_5_of_pointwise_jet_smoothing
set_option pp.proofs false in
#print PlanarNikodym.theorem_1_4_of_pointwise_jet_smoothing
set_option pp.proofs false in
#print PlanarNikodym.proposition_1_6_of_pointwise_jet_smoothing
#print axioms PlanarNikodym.exists_finite_cutoff_partition
#print axioms PlanarNikodym.Family.cutoffAverage_sum_cutoff
#print axioms PlanarNikodym.Family.auxiliaryJetNorm_sum_cutoff_le
#print axioms PlanarNikodym.Family.scaledJetNorm_sum_cutoff_le
#print axioms PlanarNikodym.jetSmoothingInput_sum_cutoff
#print axioms PlanarNikodym.jetSmoothingInput_of_local_cutoffs
#print axioms PlanarNikodym.hasFDerivAt_integral_of_compact_time_support
#print axioms PlanarNikodym.Family.fderiv_cutoffAverage_eq_integral
#print axioms PlanarNikodym.Family.fderiv_cutoffAverage_apply
#print axioms PlanarNikodym.Family.fderiv_bandAverage_apply
#print axioms PlanarNikodym.cinematicSmoothAnalysisInput_of_pointwise_jet_smoothing
#print axioms PlanarNikodym.theorem_1_5_of_pointwise_jet_smoothing
#print axioms PlanarNikodym.theorem_1_4_of_pointwise_jet_smoothing
#print axioms PlanarNikodym.proposition_1_6_of_pointwise_jet_smoothing
#check PlanarNikodym.contDiff_parameter_iteratedFDeriv
#check PlanarNikodym.integrable_parameter_iteratedFDeriv_of_compact_time_support
#check PlanarNikodym.iteratedFDeriv_integral_of_compact_time_support
#check PlanarNikodym.iteratedFDeriv_integral_apply_of_compact_time_support
#check PlanarNikodym.Family.iteratedFDeriv_cutoffAverage_eq_integral
#check PlanarNikodym.Family.auxiliary_cutoffJet_integrable
#check PlanarNikodym.Family.auxiliary_cutoffJet_eq_integral
#check PlanarNikodym.Family.auxiliary_cutoffJet_apply_eq_integral
#check PlanarNikodym.Family.auxiliary_bandJet_eq_integral
#check PlanarNikodym.iteratedFDeriv_comp_eq_sum_orderedFinpartition
set_option pp.proofs false in
#print PlanarNikodym.Family.cutoffJetAmplitude
#check PlanarNikodym.Family.auxiliary_cutoffIntegrandJet_eq_amplitude
#check PlanarNikodym.Family.cutoffJetAmplitude_integrable
#check PlanarNikodym.Family.auxiliary_cutoffJet_eq_integral_amplitude
#check PlanarNikodym.Family.auxiliary_bandJet_eq_integral_amplitude
#check PlanarNikodym.FrequencyCutoff.bandKernel_iteratedFDeriv_scaling
#check PlanarNikodym.FrequencyCutoff.norm_bandKernel_iteratedFDeriv_scaling
#check PlanarNikodym.FrequencyCutoff.integrable_norm_bandKernel_iteratedFDeriv
#check PlanarNikodym.FrequencyCutoff.integral_norm_bandKernel_iteratedFDeriv
#check PlanarNikodym.FrequencyCutoff.exists_uniform_bandKernel_jet_L1_bound
#print axioms PlanarNikodym.contDiff_parameter_iteratedFDeriv
#print axioms PlanarNikodym.integrable_parameter_iteratedFDeriv_of_compact_time_support
#print axioms PlanarNikodym.iteratedFDeriv_integral_of_compact_time_support
#print axioms PlanarNikodym.iteratedFDeriv_integral_apply_of_compact_time_support
#print axioms PlanarNikodym.Family.iteratedFDeriv_cutoffAverage_eq_integral
#print axioms PlanarNikodym.Family.auxiliary_cutoffJet_eq_integral
#print axioms PlanarNikodym.Family.auxiliary_bandJet_eq_integral
#print axioms PlanarNikodym.iteratedFDeriv_comp_eq_sum_orderedFinpartition
#print axioms PlanarNikodym.Family.auxiliary_cutoffIntegrandJet_eq_amplitude
#print axioms PlanarNikodym.Family.cutoffJetAmplitude_integrable
#print axioms PlanarNikodym.Family.auxiliary_cutoffJet_eq_integral_amplitude
#print axioms PlanarNikodym.Family.auxiliary_bandJet_eq_integral_amplitude
#print axioms PlanarNikodym.FrequencyCutoff.bandKernel_iteratedFDeriv_scaling
#print axioms PlanarNikodym.FrequencyCutoff.integrable_norm_bandKernel_iteratedFDeriv
#print axioms PlanarNikodym.FrequencyCutoff.integral_norm_bandKernel_iteratedFDeriv
#print axioms PlanarNikodym.FrequencyCutoff.exists_uniform_bandKernel_jet_L1_bound
#check PlanarNikodym.schwartzJet
#check PlanarNikodym.schwartzJet_apply
#check PlanarNikodym.iteratedFDeriv_convolution_schwartz_smul
#check PlanarNikodym.FrequencyCutoff.iteratedFDeriv_band_eq_integral
#check PlanarNikodym.lintegral_norm_average_rpow_le
#check PlanarNikodym.eLpNorm_convolution_schwartz_smul_le_of_stronglyMeasurable
#check PlanarNikodym.eLpNorm_convolution_schwartz_smul_le
#check PlanarNikodym.FrequencyCutoff.eLpNorm_iteratedFDeriv_band_le_kernel
#check PlanarNikodym.FrequencyCutoff.eLpNorm_iteratedFDeriv_band_le
#check PlanarNikodym.FrequencyCutoff.memLp_iteratedFDeriv_band
#check PlanarNikodym.FrequencyCutoff.scaled_eLpNorm_iteratedFDeriv_band_le
#check PlanarNikodym.FrequencyCutoff.scaled_band_jet_sum_le
set_option pp.proofs false in
#print PlanarNikodym.FrequencyCutoff.exists_uniform_band_jet_Lp_bound
#print axioms PlanarNikodym.schwartzJet_apply
#print axioms PlanarNikodym.iteratedFDeriv_convolution_schwartz_smul
#print axioms PlanarNikodym.FrequencyCutoff.iteratedFDeriv_band_eq_integral
#print axioms PlanarNikodym.lintegral_norm_average_rpow_le
#print axioms PlanarNikodym.eLpNorm_convolution_schwartz_smul_le_of_stronglyMeasurable
#print axioms PlanarNikodym.eLpNorm_convolution_schwartz_smul_le
#print axioms PlanarNikodym.FrequencyCutoff.eLpNorm_iteratedFDeriv_band_le_kernel
#print axioms PlanarNikodym.FrequencyCutoff.eLpNorm_iteratedFDeriv_band_le
#print axioms PlanarNikodym.FrequencyCutoff.memLp_iteratedFDeriv_band
#print axioms PlanarNikodym.FrequencyCutoff.scaled_eLpNorm_iteratedFDeriv_band_le
#print axioms PlanarNikodym.FrequencyCutoff.scaled_band_jet_sum_le
#print axioms PlanarNikodym.FrequencyCutoff.exists_uniform_band_jet_Lp_bound
#check PlanarNikodym.contDiffAt_fiber_iteratedFDeriv
#check PlanarNikodym.Family.continuousOn_cutoffGraphJet
#check PlanarNikodym.Family.exists_uniform_cutoffGraphJet_bound
#check PlanarNikodym.norm_iteratedFDeriv_jetInputProduct_le
#check PlanarNikodym.sum_norm_iteratedFDeriv_jetInputProduct_le
#check PlanarNikodym.Family.norm_cutoffJetAmplitude_le_partition_sum
set_option pp.proofs false in
#print PlanarNikodym.Family.exists_uniform_cutoffJetAmplitude_bound
#check PlanarNikodym.Family.timeInputJetMajorant_integrable
#check PlanarNikodym.Family.exists_uniform_auxiliary_cutoffJet_norm_bound
#check PlanarNikodym.planeFourierIntegral_eq_euclidean
#check PlanarNikodym.FrequencyCutoff.band_eq_fourierIntegral
#check PlanarNikodym.FrequencyCutoff.band_eq_rescaled_fourierIntegral
#check PlanarNikodym.Family.integrable_cutoffOscillatoryProduct
#check PlanarNikodym.Family.cutoffAverage_band_eq_oscillatoryIntegral
#check PlanarNikodym.Family.cutoffAverage_band_eq_rescaled_oscillatoryIntegral
#check PlanarNikodym.norm_iteratedFDeriv_planeFourierCharacter_le
#check PlanarNikodym.sum_norm_iteratedFDeriv_planeFourierCharacter_le
#check PlanarNikodym.Family.exists_uniform_cutoffJetAmplitude_fourierCharacter_bound
#check PlanarNikodym.Family.auxiliary_cutoffOscillatoryJet_eq_integral_amplitude
set_option pp.proofs false in
#print PlanarNikodym.Family.exists_uniform_auxiliary_cutoffOscillatoryJet_bound
#check PlanarNikodym.contDiff_nonstationaryAmplitude
#check PlanarNikodym.hasCompactSupport_nonstationaryAmplitude
#check PlanarNikodym.phaseOscillation_integral_eq_iterated_transfer
#check PlanarNikodym.norm_phaseOscillation_integral_le
#check PlanarNikodym.contDiff_parameterNonstationaryAmplitude
set_option pp.proofs false in
#print PlanarNikodym.exists_uniform_nonstationary_decay_constant
#check PlanarNikodym.Family.exists_uniform_nonstationary_region
#check PlanarNikodym.Family.exists_microlocal_band_split
#check PlanarNikodym.Family.cutoffAverage_band_eq_split_oscillatoryIntegral
#check PlanarNikodym.Family.cutoffOscillatoryAmplitude_nonstationary_decay
#check PlanarNikodym.Family.exists_uniform_cutoffOscillatoryAmplitude_symbol_decay
set_option pp.proofs false in
#print PlanarNikodym.Family.exists_microlocal_error_uniform_decay
#check PlanarNikodym.ProjectionModel.exists_pair_projection_patch
#check PlanarNikodym.scalar_stationary_independent_tail
#check PlanarNikodym.ProjectionModel.twoSliceCenters_independent_tail_of_stationary
#check PlanarNikodym.ProjectionModel.exists_twoSlice_center_patch
set_option pp.proofs false in
#print PlanarNikodym.ProjectionModel.exists_twoSlice_wisewell_patch
#check PlanarNikodym.ProjectionModel.incidenceTrace_hasPositivePart_of_twoSlice_stationary
#check PlanarNikodym.ProjectionModel.curveSweep_analyticSet
#check PlanarNikodym.ProjectionModel.centerSweep_analyticSet
set_option pp.proofs false in
#print PlanarNikodym.ProjectionModel.exists_null_set_of_projected_sweeps
#print axioms PlanarNikodym.contDiffAt_fiber_iteratedFDeriv
#print axioms PlanarNikodym.Family.continuousOn_cutoffGraphJet
#print axioms PlanarNikodym.Family.exists_uniform_cutoffGraphJet_bound
#print axioms PlanarNikodym.norm_iteratedFDeriv_jetInputProduct_le
#print axioms PlanarNikodym.sum_norm_iteratedFDeriv_jetInputProduct_le
#print axioms PlanarNikodym.Family.norm_cutoffJetAmplitude_le_partition_sum
#print axioms PlanarNikodym.Family.exists_uniform_cutoffJetAmplitude_bound
#print axioms PlanarNikodym.Family.timeInputJetMajorant_integrable
#print axioms PlanarNikodym.Family.exists_uniform_auxiliary_cutoffJet_norm_bound
#print axioms PlanarNikodym.planeFourierIntegral_eq_euclidean
#print axioms PlanarNikodym.FrequencyCutoff.band_eq_fourierIntegral
#print axioms PlanarNikodym.FrequencyCutoff.band_eq_rescaled_fourierIntegral
#print axioms PlanarNikodym.Family.integrable_cutoffOscillatoryProduct
#print axioms PlanarNikodym.Family.cutoffAverage_band_eq_oscillatoryIntegral
#print axioms PlanarNikodym.Family.cutoffAverage_band_eq_rescaled_oscillatoryIntegral
#print axioms PlanarNikodym.norm_iteratedFDeriv_planeFourierCharacter_le
#print axioms PlanarNikodym.sum_norm_iteratedFDeriv_planeFourierCharacter_le
#print axioms PlanarNikodym.Family.exists_uniform_cutoffJetAmplitude_fourierCharacter_bound
#print axioms PlanarNikodym.Family.auxiliary_cutoffOscillatoryJet_eq_integral_amplitude
#print axioms PlanarNikodym.Family.exists_uniform_auxiliary_cutoffOscillatoryJet_bound
#print axioms PlanarNikodym.contDiff_nonstationaryAmplitude
#print axioms PlanarNikodym.hasCompactSupport_nonstationaryAmplitude
#print axioms PlanarNikodym.phaseOscillation_integral_eq_iterated_transfer
#print axioms PlanarNikodym.norm_phaseOscillation_integral_le
#print axioms PlanarNikodym.contDiff_parameterNonstationaryAmplitude
#print axioms PlanarNikodym.exists_uniform_nonstationary_decay_constant
#print axioms PlanarNikodym.Family.exists_uniform_nonstationary_region
#print axioms PlanarNikodym.Family.exists_microlocal_band_split
#print axioms PlanarNikodym.Family.cutoffAverage_band_eq_split_oscillatoryIntegral
#print axioms PlanarNikodym.Family.cutoffOscillatoryAmplitude_nonstationary_decay
#print axioms PlanarNikodym.Family.exists_uniform_cutoffOscillatoryAmplitude_symbol_decay
#print axioms PlanarNikodym.Family.exists_microlocal_error_uniform_decay
#print axioms PlanarNikodym.ProjectionModel.exists_pair_projection_patch
#print axioms PlanarNikodym.scalar_stationary_independent_tail
#print axioms PlanarNikodym.ProjectionModel.twoSliceCenters_independent_tail_of_stationary
#print axioms PlanarNikodym.ProjectionModel.exists_twoSlice_center_patch
#print axioms PlanarNikodym.ProjectionModel.exists_twoSlice_wisewell_patch
#print axioms PlanarNikodym.ProjectionModel.incidenceTrace_hasPositivePart_of_twoSlice_stationary
#print axioms PlanarNikodym.ProjectionModel.curveSweep_analyticSet
#print axioms PlanarNikodym.ProjectionModel.centerSweep_analyticSet
#print axioms PlanarNikodym.ProjectionModel.exists_null_set_of_projected_sweeps
#check PlanarNikodym.Family.cinematicJetMap_fderiv_matrix
#check PlanarNikodym.Family.exists_cinematicJetMap_analytic_chart
#check PlanarNikodym.exists_uniform_timeTaylor_remainder_bound
#check PlanarNikodym.exists_uniform_frequency_scaled_timeTaylor_bound
#check PlanarNikodym.Family.cutoffOscillatoryAmplitude_frequency_jet_eq_integral
#check PlanarNikodym.Family.exists_uniform_cutoffOscillatoryAmplitude_scaled_frequency_jet_bound
#check PlanarNikodym.iteratedFDeriv_cexp_clm_apply
#check PlanarNikodym.norm_plane_multilinear_le_sum_basis
#check PlanarNikodym.Family.exists_uniform_cutoffOscillatoryAmplitude_symbol_frequency_jet_decay
#check PlanarNikodym.Family.exists_microlocal_error_uniform_frequency_jet_decay
#check PlanarNikodym.Family.cutoffOscillatoryErrorSchwartz_coe
#check PlanarNikodym.Family.tsupport_cutoffOscillatoryErrorSchwartz_parameters_subset
#check PlanarNikodym.exists_uniform_schwartz_seminorm_bound
#check PlanarNikodym.exists_schwartz_clm_finite_bound
#check PlanarNikodym.exists_compact_schwartz_clm_decay_constant
#check PlanarNikodym.planeInverseFourierSchwartzCLM_apply
#check PlanarNikodym.exists_uniform_complex_symbol_kernel_Lp_decay
#check PlanarNikodym.scaledSymbolOperator_eq_kernel
#check PlanarNikodym.scaledSymbolOperator_enorm_le
#check PlanarNikodym.exists_compact_symbol_operator_Lp_decay
#check PlanarNikodym.Family.exists_uniform_nonstationary_error_kernel_Lp_decay
#check PlanarNikodym.Family.cutoffAverage_band_eq_partialExtension_add_error
#check PlanarNikodym.Family.exists_microlocal_error_Lp_decay
#check PlanarNikodym.Family.cutoffAverage_band_sub_partialExtension_eq_error
#check PlanarNikodym.Family.exists_band_partialExtension_error_bound
#check PlanarNikodym.Wisewell.card_factorialPrefix
#check PlanarNikodym.Wisewell.range_factorialValue
#check PlanarNikodym.Wisewell.norm_factorialSelector_sub_sum_le_of_bounded
#check PlanarNikodym.Wisewell.boundedCoefficientSchedule_affine_cancellation
#check PlanarNikodym.Wisewell.measurable_boundedFactorialChoice
#check PlanarNikodym.Wisewell.fst_image_boundedFactorialGraph
#check PlanarNikodym.Wisewell.isCompact_boundedFactorialSweep
#print axioms PlanarNikodym.Family.cinematicJetMap_fderiv_matrix
#print axioms PlanarNikodym.Family.exists_cinematicJetMap_analytic_chart
#print axioms PlanarNikodym.exists_uniform_timeTaylor_remainder_bound
#print axioms PlanarNikodym.exists_uniform_frequency_scaled_timeTaylor_bound
#print axioms PlanarNikodym.Family.cutoffOscillatoryAmplitude_frequency_jet_eq_integral
#print axioms PlanarNikodym.Family.exists_uniform_cutoffOscillatoryAmplitude_scaled_frequency_jet_bound
#print axioms PlanarNikodym.iteratedFDeriv_cexp_clm_apply
#print axioms PlanarNikodym.norm_plane_multilinear_le_sum_basis
#print axioms PlanarNikodym.Family.exists_uniform_cutoffOscillatoryAmplitude_symbol_frequency_jet_decay
#print axioms PlanarNikodym.Family.exists_microlocal_error_uniform_frequency_jet_decay
#print axioms PlanarNikodym.Family.cutoffOscillatoryErrorSchwartz_coe
#print axioms PlanarNikodym.Family.tsupport_cutoffOscillatoryErrorSchwartz_parameters_subset
#print axioms PlanarNikodym.exists_uniform_schwartz_seminorm_bound
#print axioms PlanarNikodym.exists_schwartz_clm_finite_bound
#print axioms PlanarNikodym.exists_compact_schwartz_clm_decay_constant
#print axioms PlanarNikodym.planeInverseFourierSchwartzCLM_apply
#print axioms PlanarNikodym.exists_uniform_complex_symbol_kernel_Lp_decay
#print axioms PlanarNikodym.scaledSymbolOperator_eq_kernel
#print axioms PlanarNikodym.scaledSymbolOperator_enorm_le
#print axioms PlanarNikodym.exists_compact_symbol_operator_Lp_decay
#print axioms PlanarNikodym.Family.exists_uniform_nonstationary_error_kernel_Lp_decay
#print axioms PlanarNikodym.Family.cutoffAverage_band_eq_partialExtension_add_error
#print axioms PlanarNikodym.Family.exists_microlocal_error_Lp_decay
#print axioms PlanarNikodym.Family.cutoffAverage_band_sub_partialExtension_eq_error
#print axioms PlanarNikodym.Family.exists_band_partialExtension_error_bound
#print axioms PlanarNikodym.Wisewell.card_factorialPrefix
#print axioms PlanarNikodym.Wisewell.range_factorialValue
#print axioms PlanarNikodym.Wisewell.norm_factorialSelector_sub_sum_le_of_bounded
#print axioms PlanarNikodym.Wisewell.boundedCoefficientSchedule_affine_cancellation
#print axioms PlanarNikodym.Wisewell.measurable_boundedFactorialChoice
#print axioms PlanarNikodym.Wisewell.fst_image_boundedFactorialGraph
#print axioms PlanarNikodym.Wisewell.isCompact_boundedFactorialSweep
set_option pp.proofs false in
#print PlanarNikodym.Family.exists_band_partialExtension_error_bound
set_option pp.proofs false in
#print PlanarNikodym.Wisewell.boundedCoefficientSchedule_affine_cancellation
#check PlanarNikodym.Wisewell.norm_factorialPoint_sub_prefix_le
#check PlanarNikodym.Wisewell.exists_uniform_affine_remainder
#check PlanarNikodym.Wisewell.norm_linear_factorialPoint_tail_le
#check PlanarNikodym.Wisewell.exists_factorial_prefix_cover
#check PlanarNikodym.Wisewell.volume_image_boundedFactorialGraph_eq_zero
#check PlanarNikodym.Wisewell.volume_boundedFactorialSweep_eq_zero
#check PlanarNikodym.Wisewell.exists_compact_null_curves_of_bounded_slope
#print axioms PlanarNikodym.Wisewell.norm_factorialPoint_sub_prefix_le
#print axioms PlanarNikodym.Wisewell.exists_uniform_affine_remainder
#print axioms PlanarNikodym.Wisewell.norm_linear_factorialPoint_tail_le
#print axioms PlanarNikodym.Wisewell.exists_factorial_prefix_cover
#print axioms PlanarNikodym.Wisewell.volume_image_boundedFactorialGraph_eq_zero
#print axioms PlanarNikodym.Wisewell.volume_boundedFactorialSweep_eq_zero
#print axioms PlanarNikodym.Wisewell.exists_compact_null_curves_of_bounded_slope
set_option pp.proofs false in
#print PlanarNikodym.Wisewell.exists_compact_null_curves_of_bounded_slope
#check PlanarNikodym.exists_scaleTimeCutoff_partition
#check PlanarNikodym.scaleTimeCutoff_overlap_le_three
#check PlanarNikodym.exists_uniform_scaleTimeCutoff_deriv_bound
#check PlanarNikodym.Family.cutoffOscillatoryAmplitude_eq_sum_scaleTimeLocalized
#check PlanarNikodym.timeTaylor_remainder_eq_integral
#check PlanarNikodym.contDiff_timeTaylorIntegralRemainder
#check PlanarNikodym.exists_uniform_local_criticalTaylorCorrection_jet_bound
#check PlanarNikodym.exists_uniform_critical_rescaledTaylorAmplitude_jet_bound
#check PlanarNikodym.phase_mul_amplitude_eq_taylor_rescaled
#check PlanarNikodym.timeJetParameterMatrix_timeTaylorEval_center
#check PlanarNikodym.det_timeJetParameterMatrix_rescaled_timeTaylorEval_center
#check PlanarNikodym.exists_uniform_timeTaylor_minor_lower_bound
#print axioms PlanarNikodym.exists_scaleTimeCutoff_partition
#print axioms PlanarNikodym.scaleTimeCutoff_overlap_le_three
#print axioms PlanarNikodym.exists_uniform_scaleTimeCutoff_deriv_bound
#print axioms PlanarNikodym.Family.cutoffOscillatoryAmplitude_eq_sum_scaleTimeLocalized
#print axioms PlanarNikodym.timeTaylor_remainder_eq_integral
#print axioms PlanarNikodym.contDiff_timeTaylorIntegralRemainder
#print axioms PlanarNikodym.exists_uniform_local_criticalTaylorCorrection_jet_bound
#print axioms PlanarNikodym.exists_uniform_critical_rescaledTaylorAmplitude_jet_bound
#print axioms PlanarNikodym.phase_mul_amplitude_eq_taylor_rescaled
#print axioms PlanarNikodym.timeJetParameterMatrix_timeTaylorEval_center
#print axioms PlanarNikodym.det_timeJetParameterMatrix_rescaled_timeTaylorEval_center
#print axioms PlanarNikodym.exists_uniform_timeTaylor_minor_lower_bound
#check PlanarNikodym.exists_initial_coordinate_minor
#check PlanarNikodym.Family.exists_finite_cinematicInitialMinor_cutoff_partition
#check PlanarNikodym.Family.exists_regular_lowerCinematicJetMap_chart
#check PlanarNikodym.Family.det_lowerCinematicJetMap_fderiv_zero
#check PlanarNikodym.map_coefficientDilation_volume
#check PlanarNikodym.coefficientDilation_image_box
#check PlanarNikodym.norm_iteratedFDeriv_comp_lowerDegreeDilation_symm_le
#check PlanarNikodym.critical_effective_frequency_ge_one
#check PlanarNikodym.Family.frequency_timeTaylorEval_in_scaled_lower_chart
#check PlanarNikodym.Family.exists_finite_cinematic_regular_time_partition
#check PlanarNikodym.exists_compact_analytic_chartJacobian_bounds
#check PlanarNikodym.integral_scaled_analytic_chart_target
#check PlanarNikodym.lintegral_scaled_analytic_chart_target
#print axioms PlanarNikodym.exists_initial_coordinate_minor
#print axioms PlanarNikodym.Family.exists_finite_cinematicInitialMinor_cutoff_partition
#print axioms PlanarNikodym.Family.exists_regular_lowerCinematicJetMap_chart
#print axioms PlanarNikodym.Family.det_lowerCinematicJetMap_fderiv_zero
#print axioms PlanarNikodym.map_coefficientDilation_volume
#print axioms PlanarNikodym.coefficientDilation_image_box
#print axioms PlanarNikodym.norm_iteratedFDeriv_comp_lowerDegreeDilation_symm_le
#print axioms PlanarNikodym.critical_effective_frequency_ge_one
#print axioms PlanarNikodym.Family.frequency_timeTaylorEval_in_scaled_lower_chart
#print axioms PlanarNikodym.Family.exists_finite_cinematic_regular_time_partition
#print axioms PlanarNikodym.exists_compact_analytic_chartJacobian_bounds
#print axioms PlanarNikodym.integral_scaled_analytic_chart_target
#print axioms PlanarNikodym.lintegral_scaled_analytic_chart_target
#check PlanarNikodym.Family.exists_uniform_movingLowerJet_chart
#check PlanarNikodym.Family.exists_finite_movingChart_cutoff_partition
#check PlanarNikodym.Family.exists_uniform_lowerDegree_extension_Lp_reduction
#check PlanarNikodym.Family.cutoffPartialExtension_lowerDegree_Lp_reduction
#check PlanarNikodym.exists_uniform_critical_inverseChartTaylorAmplitude_jet_bound
#print axioms PlanarNikodym.retainedParameterMap_fderiv_isInvertible
#print axioms PlanarNikodym.Family.exists_movingLowerJet_analytic_chart
#print axioms PlanarNikodym.exists_uniform_fiberChartJacobian_bounds
#print axioms PlanarNikodym.Family.exists_uniform_movingLowerJet_chart
#print axioms PlanarNikodym.Family.exists_finite_movingChart_cutoff_partition
#print axioms PlanarNikodym.coefficientBoxCutoff_overlap_le
#print axioms PlanarNikodym.exists_uniform_coefficientBoxCutoff_jet_bound
#print axioms PlanarNikodym.sum_coefficientBox_lintegral_le
#print axioms PlanarNikodym.polynomialExtension_boxPartition_eLpNorm_le
#print axioms PlanarNikodym.exists_uniform_critical_inverseChartTaylorAmplitude_jet_bound
#print axioms PlanarNikodym.exists_local_smooth_Taylor_amplitude
#print axioms PlanarNikodym.parameterFrame_volume_preserving
#print axioms PlanarNikodym.Family.lintegral_cutoffPartialExtension_selected_parameters
#print axioms PlanarNikodym.Family.exists_cutoffPartialExtension_time_partition
#print axioms PlanarNikodym.Family.exists_uniform_lowerDegree_extension_Lp_reduction
#print axioms PlanarNikodym.Family.cutoffPartialExtension_lowerDegree_Lp_reduction
#print axioms PlanarNikodym.eLpNorm_timeDataRescaling
#print axioms PlanarNikodym.exists_Fourier_criticalTimeScale_threshold
#check PlanarNikodym.det_momentSamplingMatrix
#check PlanarNikodym.exists_uniform_momentSampling_perturbation
#check PlanarNikodym.det_fderiv_momentTimeJet
#check PlanarNikodym.timeSliceExtension_moment_eLpNorm_rescale
#check PlanarNikodym.finite_l2_le_card_mul_lp
#print axioms PlanarNikodym.abs_det_momentSamplingMatrix_lower_bound
#print axioms PlanarNikodym.exists_uniform_momentSampling_perturbation
#print axioms PlanarNikodym.jetPolynomial_momentTranslation
#print axioms PlanarNikodym.det_momentTranslation
#print axioms PlanarNikodym.det_fderiv_momentTimeJet
#print axioms PlanarNikodym.jetPolynomial_parabolic_rescale
#print axioms PlanarNikodym.det_momentParabolicMap_eq
#print axioms PlanarNikodym.map_momentParabolicMap_volume
#print axioms PlanarNikodym.timeSliceExtension_moment_rescale
#print axioms PlanarNikodym.timeSliceExtension_moment_eLpNorm_rescale
#print axioms PlanarNikodym.finite_l2_le_card_mul_lp
#print axioms PlanarNikodym.coneDecouplingExponent_split
#check PlanarNikodym.exists_uniform_timeLocalized_weightedPartialFourierData_L2_mass_bound
#check PlanarNikodym.det_timeFrequencyMixedMatrix
#check PlanarNikodym.ProjectionModel.exists_null_set_of_twoSlice_stationary
#check PlanarNikodym.Family.RanTame
#check PlanarNikodym.Family.ranTame_seed_ball
#check PlanarNikodym.Family.ranTame_seed
#check PlanarNikodym.AnalyticPiece.ranTame
#print axioms PlanarNikodym.lintegral_partialFourierData_plane_sq
#print axioms PlanarNikodym.eLpNorm_partialFourierData_two
#print axioms PlanarNikodym.sum_timeLocalizedData_eLpNorm_two_sq_le
#print axioms PlanarNikodym.exists_uniform_timeLocalized_weightedPartialFourierData_L2_mass_bound
#print axioms PlanarNikodym.det_timeFrequencyMixedMatrix
#print axioms PlanarNikodym.Wisewell.exists_compact_null_curves_on_regular_box
#print axioms PlanarNikodym.ProjectionModel.exists_compact_null_twoSlice_curves
#print axioms PlanarNikodym.ProjectionModel.exists_null_set_of_twoSlice_stationary
#print axioms PlanarNikodym.exists_ranDefinableOn_nhds_of_compact
#print axioms PlanarNikodym.Family.ranTame_seed_ball
#print axioms PlanarNikodym.Family.ranTame_seed
#print axioms PlanarNikodym.Family.RanTame.pullback
#print axioms PlanarNikodym.AnalyticPiece.ranTame
#check PlanarNikodym.Family.timeSliceChartGeometry_retained
#check PlanarNikodym.Family.exists_uniform_movingChart_main_square_sum_bound
#check PlanarNikodym.Family.exists_finite_cinematic_main_L2_partition
#check PlanarNikodym.Family.exists_finite_cinematic_critical_main_L2_partition
#print axioms PlanarNikodym.fourierIntegral_ae_eq_L2
#print axioms PlanarNikodym.fourierInvIntegral_ae_eq_L2
#print axioms PlanarNikodym.lintegral_planeInverseFourierIntegral_sq
#print axioms PlanarNikodym.lintegral_weightedPartialFourierData_sq_le_of_integrable
#print axioms PlanarNikodym.integrable_timeRestricted_weightedPartialFourierData
#print axioms PlanarNikodym.lintegral_coneFrequencyData_sq
#print axioms PlanarNikodym.lintegral_linearConeExtension_sq_le_of_integrable
#print axioms PlanarNikodym.jointAmplitudeFourier_reconstruction
#print axioms PlanarNikodym.eLpNorm_amplitudeConeExtension_two_le
#print axioms PlanarNikodym.exists_uniform_jointAmplitudeFourier_L1_bound
#print axioms PlanarNikodym.compactSmoothAmplitudeFamily_uniform_support_and_jets
#print axioms PlanarNikodym.exists_uniform_local_inverseChart_amplitude_cone_bound
#print axioms PlanarNikodym.Family.exists_uniform_local_linear_chart_slice_sq_bound
#print axioms PlanarNikodym.timeSliceExtension_timeRestrictedData
#print axioms PlanarNikodym.Family.exists_uniform_local_timeSlice_square_sum_bound
#print axioms PlanarNikodym.Family.exists_uniform_cutoffPartialExtension_square_sum_bound
#print axioms PlanarNikodym.Family.timeSliceChartGeometry_retained
#print axioms PlanarNikodym.Family.exists_uniform_movingChart_main_square_sum_bound
#print axioms PlanarNikodym.Family.exists_finite_cinematic_main_L2_partition
#print axioms PlanarNikodym.Family.exists_finite_cinematic_critical_main_L2_partition
#check PlanarNikodym.RanDefinable.closure
#check PlanarNikodym.RanDefinableOn.directionalDerivative
#check PlanarNikodym.DoubleRankMinor.ranDefinable_regularSet
#check PlanarNikodym.ranDefinable_center_image_closure
#check PlanarNikodym.exists_auxiliary_partial_zero_piece
#check PlanarNikodym.exists_finite_regular_auxiliary_zero_cover
#check PlanarNikodym.closure_smooth_image_null_of_compact_container
#check PlanarNikodym.analytic_parameter_arc_center_closure_null
#print axioms PlanarNikodym.RanDefinable.closure
#print axioms PlanarNikodym.RanDefinableOn.directionalDerivative
#print axioms PlanarNikodym.DoubleRankMinor.ranDefinable_regularSet
#print axioms PlanarNikodym.ranDefinable_center_image_closure
#print axioms PlanarNikodym.exists_auxiliary_partial_zero_piece
#print axioms PlanarNikodym.exists_finite_regular_auxiliary_zero_cover
#print axioms PlanarNikodym.closure_smooth_image_null_of_compact_container
#print axioms PlanarNikodym.analytic_parameter_arc_center_closure_null
#check PlanarNikodym.analytic_eventually_zero_of_coordinateJets_zero
#check PlanarNikodym.exists_uniform_nonzero_coordinateJet_order
#check PlanarNikodym.analytic_zero_set_null
#check PlanarNikodym.RanDefinableOn.coordinateJet
#check PlanarNikodym.flatFiberCenters_closure_null_on_compact
#check PlanarNikodym.exists_ranDefinable_closed_null_flat_fiber_exception
#check PlanarNikodym.auxiliary_zero_flat_or_regularJet
#check PlanarNikodym.auxiliary_zero_flat_or_lower_piece
#check PlanarNikodym.exists_uniform_regular_auxiliaryJet_order
#check PlanarNikodym.RanDefinableOn.auxiliaryJet
#check PlanarNikodym.DoubleRankMinor.exists_patch_exception_pieces_and_compact_order
#print axioms PlanarNikodym.analytic_eventually_zero_of_coordinateJets_zero
#print axioms PlanarNikodym.exists_regular_coordinateJet_at_zero
#print axioms PlanarNikodym.analytic_zero_set_null
#print axioms PlanarNikodym.RanDefinableOn.coordinateJet
#print axioms PlanarNikodym.flatFiberCenters_closure_null_on_compact
#print axioms PlanarNikodym.exists_ranDefinable_closed_null_flat_fiber_exception
#print axioms PlanarNikodym.auxiliary_zero_flat_or_regularJet
#print axioms PlanarNikodym.exists_regular_auxiliary_coordinate_zero_piece
#print axioms PlanarNikodym.auxiliary_zero_flat_or_lower_piece
#print axioms PlanarNikodym.exists_uniform_regular_auxiliaryJet_order
#print axioms PlanarNikodym.RanDefinableOn.auxiliaryJet
#print axioms PlanarNikodym.ranDefinable_regular_auxiliaryJet_zero_locus
#print axioms PlanarNikodym.DoubleRankMinor.exists_patch_exception_and_lower_pieces
#print axioms PlanarNikodym.DoubleRankMinor.exists_patch_exception_pieces_and_compact_order
#check PlanarNikodym.DoubleRankMinor.exists_local_flat_exception
#check PlanarNikodym.DoubleRankMinor.exists_compact_exception_and_nonflat
#check PlanarNikodym.DoubleRankMinor.exists_compact_exception_pieces_and_order
#print axioms PlanarNikodym.DoubleRankMinor.exists_local_flat_exception
#print axioms PlanarNikodym.DoubleRankMinor.exists_compact_exception_and_nonflat
#print axioms PlanarNikodym.DoubleRankMinor.exists_compact_exception_pieces_and_order
#check PlanarNikodym.glyz_schwartz_reproducing
#check PlanarNikodym.glyz_uncertainty_fourier_box
#check PlanarNikodym.glyz_moment_uncertainty
#check PlanarNikodym.integral_glyzPolarWeight
#check PlanarNikodym.glyz_dyadic_whitney_identity
#check PlanarNikodym.glyz_bilinear_to_linear
#check PlanarNikodym.glyz_bilinear_to_linear_geometric
#check PlanarNikodym.eLpNorm_glyzSchwartzFrequencyAffine
#check PlanarNikodym.det_gram_glyzOrthogonalCurve_ne_zero
#print axioms PlanarNikodym.glyz_uncertainty_fourier_box
#print axioms PlanarNikodym.glyz_bilinear_to_linear_geometric
#print axioms PlanarNikodym.det_gram_glyzOrthogonalCurve_ne_zero
#check PlanarNikodym.glyz_affine_decoupling_transfer
#print axioms PlanarNikodym.glyz_affine_decoupling_transfer
#check PlanarNikodym.exists_uniform_glyzCoordinateCurve_certificate
#check PlanarNikodym.exists_uniform_glyzCoordinateCurve_inverse
#check PlanarNikodym.exists_uniform_glyzTaylorCurve_inverse
#check PlanarNikodym.exists_uniform_glyzCurveBox_taylor_inclusion
#check PlanarNikodym.glyzTaylorCurveBox_eq_affine_momentBox
#check PlanarNikodym.glyzMomentFrequencyBox_affine_image
#check PlanarNikodym.glyz_asymmetric_holder_recursion
#check PlanarNikodym.glyz_polar_asymmetric_holder
#check PlanarNikodym.glyz_polar_bilinear_lt_top
#check PlanarNikodym.glyz_finite_bootstrap_zero
#print axioms PlanarNikodym.exists_uniform_glyzCoordinateCurve_certificate
#print axioms PlanarNikodym.exists_uniform_glyzCurveBox_taylor_inclusion
#print axioms PlanarNikodym.glyzTaylorCurveBox_eq_affine_momentBox
#print axioms PlanarNikodym.glyzMomentFrequencyBox_affine_image
#print axioms PlanarNikodym.glyz_asymmetric_holder_recursion
#print axioms PlanarNikodym.glyz_polar_bilinear_lt_top
#print axioms PlanarNikodym.glyz_finite_bootstrap_zero
#check PlanarNikodym.fourierInv_glyzFourierMarginal
#check PlanarNikodym.glyzSlice_fourier_support_projection
#check PlanarNikodym.glyzSubspaceSlice_fourier_support
#print axioms PlanarNikodym.fourierInv_glyzFourierMarginal
#print axioms PlanarNikodym.glyzSubspaceSlice_fourier_support
#check PlanarNikodym.glyz_lintegral_weighted_mixed_l2
#check PlanarNikodym.glyzSubspaceAverage_pairing
#check PlanarNikodym.exists_uniform_glyzTransverse_coordinates
#check PlanarNikodym.exists_uniform_glyz_transverse_weight
#check PlanarNikodym.exists_uniform_glyz_transverse_powerAverage
#check PlanarNikodym.exists_uniform_glyz_transverse_mixed_l2
#check PlanarNikodym.exists_uniform_glyz_projected_frequencyBox
#check PlanarNikodym.exists_uniform_glyzProjectedSlice_support
#print axioms PlanarNikodym.glyz_lintegral_weighted_mixed_l2
#print axioms PlanarNikodym.glyzSubspaceAverage_pairing
#print axioms PlanarNikodym.exists_uniform_glyz_transverse_weight
#print axioms PlanarNikodym.exists_uniform_glyz_transverse_mixed_l2
#print axioms PlanarNikodym.exists_uniform_glyzProjectedSlice_support
#check PlanarNikodym.det_glyzMomentFrequencyFrame
#check PlanarNikodym.exists_uniform_glyzMomentCoordinates_nested
#check PlanarNikodym.glyzPolarWeight_two_region
#check PlanarNikodym.exists_uniform_glyz_closedInterval_convolution
#check PlanarNikodym.exists_uniform_glyz_nested_powerAverage
#check PlanarNikodym.exists_uniform_glyz_parent_powerAverage_le_child
#check PlanarNikodym.isProbabilityMeasure_glyzBallMeasure
#check PlanarNikodym.exists_uniform_glyz_transverse_powerAverage_shift
#check PlanarNikodym.exists_uniform_glyz_transverse_localize
#check PlanarNikodym.glyz_integrated_local_decoupling
#check PlanarNikodym.exists_uniform_glyz_lower_degree_assembly
#print axioms PlanarNikodym.exists_uniform_glyzMomentCoordinates_nested
#print axioms PlanarNikodym.exists_uniform_glyz_closedInterval_convolution
#print axioms PlanarNikodym.exists_uniform_glyz_parent_powerAverage_le_child
#print axioms PlanarNikodym.exists_uniform_glyz_transverse_localize
#print axioms PlanarNikodym.exists_uniform_glyz_lower_degree_assembly
#check PlanarNikodym.exists_separated_scalar_uniform_transverse_cone
#print axioms PlanarNikodym.exists_separated_scalar_uniform_transverse_cone
#check PlanarNikodym.exists_uniform_family_thinSegmentTube_compression_of_witness
#print axioms PlanarNikodym.exists_uniform_family_thinSegmentTube_compression_of_witness
#check PlanarNikodym.exists_finite_blind_replacement_family
#print axioms PlanarNikodym.exists_finite_blind_replacement_family
#check PlanarNikodym.lintegral_blind_projection_pos
#print axioms PlanarNikodym.lintegral_blind_projection_pos
#check PlanarNikodym.finite_blind_descendants_subset_fixed_tube
#print axioms PlanarNikodym.finite_blind_descendants_subset_fixed_tube
#check PlanarNikodym.VenetianBlindTree.volume_projected_leafUnion_le
#print axioms PlanarNikodym.VenetianBlindTree.volume_projected_leafUnion_le
#check PlanarNikodym.finite_blind_length_le_exp
#print axioms PlanarNikodym.finite_blind_length_le_exp
#check PlanarNikodym.exists_compact_prescribedProjection_of_refinement
#print axioms PlanarNikodym.exists_compact_prescribedProjection_of_refinement
#check PlanarNikodym.exists_borel_prescribedProjection_of_compact_system
#print axioms PlanarNikodym.exists_borel_prescribedProjection_of_compact_system
#check PlanarNikodym.exists_reparametrizeScalarProjection_patch
#print axioms PlanarNikodym.exists_reparametrizeScalarProjection_patch
#check PlanarNikodym.exists_uniform_blind_branch_compression
#print axioms PlanarNikodym.exists_uniform_blind_branch_compression
#check PlanarNikodym.exists_iterated_blind_replacement_shrinking
#print axioms PlanarNikodym.exists_iterated_blind_replacement_shrinking
#check PlanarNikodym.DyadicBlindTrace.volume_terminalUnion_le
#print axioms PlanarNikodym.DyadicBlindTrace.volume_terminalUnion_le
#check PlanarNikodym.DyadicBlindTrace.exists_uniform_thickened_projection_bound
#print axioms PlanarNikodym.DyadicBlindTrace.exists_uniform_thickened_projection_bound
#check PlanarNikodym.exists_uniform_small_projection_segment_fan
#print axioms PlanarNikodym.exists_uniform_small_projection_segment_fan
#check PlanarNikodym.exists_compact_zero_positive_projection_of_local_fans
#print axioms PlanarNikodym.exists_compact_zero_positive_projection_of_local_fans
#check PlanarNikodym.LocalTransverseProjectionData.exists_compact_zero_positive_projection
#print axioms PlanarNikodym.LocalTransverseProjectionData.exists_compact_zero_positive_projection
#check PlanarNikodym.ProjectionModel.exists_null_set_positive_incidenceTrace
#print axioms PlanarNikodym.ProjectionModel.exists_null_set_positive_incidenceTrace
#check PlanarNikodym.projection_construction_input
#print axioms PlanarNikodym.projection_construction_input
#check PlanarNikodym.theorem_1_5_case_positive_intermediate_proved
#print axioms PlanarNikodym.theorem_1_5_case_positive_intermediate_proved
#check PlanarNikodym.theorem_1_5_after_projection
#check PlanarNikodym.theorem_1_4_after_projection
#check PlanarNikodym.proposition_1_6_after_projection
#print axioms PlanarNikodym.theorem_1_5_after_projection
#print axioms PlanarNikodym.theorem_1_4_after_projection
#print axioms PlanarNikodym.proposition_1_6_after_projection
#check PlanarNikodym.glyzOptimalSquareLoss_l2_eq_zero
#check PlanarNikodym.glyzOptimalAsymmetricLoss_le_linear
#check PlanarNikodym.glyz_critical_optimal_holder_recursion
#check PlanarNikodym.glyz_fixed_depth_bilinear_of_optimal_asymmetric_loss
#check PlanarNikodym.exists_glyz_dyadic_radius_reduction
#check PlanarNikodym.glyz_enlarged_affine_dyadic_decoupling_of_admissible_square_loss
#check PlanarNikodym.glyz_controlled_curve_decoupling_of_moment_optimal_zero
#check PlanarNikodym.glyz_controlled_curve_translated_normalized_local_of_moment_optimal_zero
#check PlanarNikodym.strong_L2_LInfinity_interpolation
#check PlanarNikodym.Family.exists_finite_cinematic_critical_main_Lp_decay_partition
#print axioms PlanarNikodym.glyz_fixed_depth_bilinear_of_optimal_asymmetric_loss
#print axioms PlanarNikodym.glyz_enlarged_affine_dyadic_decoupling_of_admissible_square_loss
#print axioms PlanarNikodym.glyz_controlled_curve_translated_normalized_local_of_moment_optimal_zero
#print axioms PlanarNikodym.strong_L2_LInfinity_interpolation
#print axioms PlanarNikodym.Family.exists_finite_cinematic_critical_main_Lp_decay_partition
#check PlanarNikodym.exists_uniform_glyz_slice_local_decoupling
#check PlanarNikodym.exists_uniform_glyz_lower_degree_decoupling
#check PlanarNikodym.exists_uniform_glyz_dyadic_lower_degree
#check PlanarNikodym.exists_uniform_glyz_asymmetric_lower_degree_gain
#check PlanarNikodym.glyz_critical_optimal_gain
#check PlanarNikodym.glyzOptimalSquareLoss_le_asymmetric
#check PlanarNikodym.glyzCriticalSignedDeviation_boundedBelow
#check PlanarNikodym.glyzCriticalSignedDeviation_boundedAbove
#check PlanarNikodym.glyz_signed_functional_bootstrap_zero
#check PlanarNikodym.glyz_critical_optimal_square_loss_eq_zero
#check PlanarNikodym.glyz_critical_admissible_square_loss
#check PlanarNikodym.glyz_critical_moment_decoupling
#print axioms PlanarNikodym.exists_uniform_glyz_slice_local_decoupling
#print axioms PlanarNikodym.exists_uniform_glyz_dyadic_lower_degree
#print axioms PlanarNikodym.glyz_critical_optimal_gain
#print axioms PlanarNikodym.glyzOptimalSquareLoss_le_asymmetric
#print axioms PlanarNikodym.glyz_signed_functional_bootstrap_zero
#print axioms PlanarNikodym.glyz_critical_optimal_square_loss_eq_zero
#print axioms PlanarNikodym.glyz_critical_moment_decoupling
#check PlanarNikodym.glyz_supercritical_moment_decoupling
#print axioms PlanarNikodym.glyz_supercritical_moment_decoupling
#check PlanarNikodym.glyz_general_curve_critical_decoupling
#print axioms PlanarNikodym.glyz_general_curve_critical_decoupling
#check PlanarNikodym.glyz_supercritical_curve_decoupling
#print axioms PlanarNikodym.glyz_supercritical_curve_decoupling
#check PlanarNikodym.glyz_cone_critical_decoupling
#print axioms PlanarNikodym.glyz_cone_critical_decoupling
#check PlanarNikodym.glyz_supercritical_cone_decoupling
#print axioms PlanarNikodym.glyz_supercritical_cone_decoupling
#check PlanarNikodym.glyz_cone_spectral_local_lp
#print axioms PlanarNikodym.glyz_cone_spectral_local_lp
#check PlanarNikodym.exists_uniform_oscillatoryConeExtension_fourier_tail
#print axioms PlanarNikodym.exists_uniform_oscillatoryConeExtension_fourier_tail
#check PlanarNikodym.glyz_oscillatory_cone_local_lp
#print axioms PlanarNikodym.glyz_oscillatory_cone_local_lp
#check PlanarNikodym.glyz_parabolic_global_lp_L1_error
#print axioms PlanarNikodym.glyz_parabolic_global_lp_L1_error
#check PlanarNikodym.Family.exists_movingLowerJet_smooth_chart
#print axioms PlanarNikodym.Family.exists_movingLowerJet_smooth_chart
#check PlanarNikodym.Family.exists_glyz_raw_chart_parent_step
#print axioms PlanarNikodym.Family.exists_glyz_raw_chart_parent_step
#check PlanarNikodym.glyz_chart_parabolic_error_le
#print axioms PlanarNikodym.glyz_chart_parabolic_error_le
#check PlanarNikodym.Family.exists_glyz_original_parent_step
#print axioms PlanarNikodym.Family.exists_glyz_original_parent_step
#check PlanarNikodym.Family.exists_glyz_original_epsilon_power
#print axioms PlanarNikodym.Family.exists_glyz_original_epsilon_power
#check PlanarNikodym.Family.exists_glyz_original_epsilon_power_coarse
#print axioms PlanarNikodym.Family.exists_glyz_original_epsilon_power_coarse
#check PlanarNikodym.Family.exists_glyz_original_injected_coarse_power
#print axioms PlanarNikodym.Family.exists_glyz_original_injected_coarse_power
#check PlanarNikodym.exists_glyz_standard_grid_assignment
#print axioms PlanarNikodym.exists_glyz_standard_grid_assignment
#check PlanarNikodym.glyzRawExtension_exactTimePiece_eq_timeSliceExtension
#print axioms PlanarNikodym.glyzRawExtension_exactTimePiece_eq_timeSliceExtension
#check PlanarNikodym.Family.exists_glyz_exact_scale_power
#print axioms PlanarNikodym.Family.exists_glyz_exact_scale_power
#check PlanarNikodym.Family.exists_glyz_exact_scale_decoupling
#print axioms PlanarNikodym.Family.exists_glyz_exact_scale_decoupling
#check PlanarNikodym.Family.exists_glyz_global_smooth_phase
#print axioms PlanarNikodym.Family.exists_glyz_global_smooth_phase
#check PlanarNikodym.Family.lemma_2_3
#print axioms PlanarNikodym.Family.lemma_2_3
#check PlanarNikodym.Family.exists_glyz_lower_original_parent_step
#check PlanarNikodym.Family.glyz_cascade_decoupling
#check PlanarNikodym.Family.exists_full_cinematic_small_main_Lp
#check PlanarNikodym.Family.exists_positive_radial_main_eLp_smoothing_nat
#check PlanarNikodym.Family.exists_zero_dim_positive_main_eLp_smoothing_nat
#check PlanarNikodym.Family.exists_partialExtension_global_Lp_of_L1_error
#check PlanarNikodym.Family.exists_two_sided_main_global_smoothing
#check PlanarNikodym.Family.exists_scalar_weighted_smoothing_neighborhood
#check PlanarNikodym.Family.exists_jet_smoothing_neighborhood
#check PlanarNikodym.pointwise_jet_smoothing_input
#check PlanarNikodym.Family.theorem_2_1_proved
#check PlanarNikodym.cinematic_smooth_analysis_input
#check PlanarNikodym.cinematic_null_input
#check PlanarNikodym.theorem_1_5_proved
#check PlanarNikodym.theorem_1_4_of_connected_cells
#check PlanarNikodym.proposition_1_6_of_analytic_cells
#print axioms PlanarNikodym.Family.exists_two_sided_main_global_smoothing
#print axioms PlanarNikodym.Family.theorem_2_1_proved
#print axioms PlanarNikodym.pointwise_jet_smoothing_input
#print axioms PlanarNikodym.cinematic_smooth_analysis_input
#print axioms PlanarNikodym.theorem_1_5_proved
#print axioms PlanarNikodym.theorem_1_4_of_connected_cells
#print axioms PlanarNikodym.proposition_1_6_of_analytic_cells
#check PlanarNikodym.exists_countable_regular_auxiliary_zero_pieces
#print axioms PlanarNikodym.exists_countable_regular_auxiliary_zero_pieces
#check PlanarNikodym.exists_countable_nonflat_auxiliary_zero_pieces
#print axioms PlanarNikodym.exists_countable_nonflat_auxiliary_zero_pieces
#check PlanarNikodym.exists_null_flat_auxiliary_fiber_exception
#print axioms PlanarNikodym.exists_null_flat_auxiliary_fiber_exception
#check PlanarNikodym.Family.exists_countable_rank_step
#print axioms PlanarNikodym.Family.exists_countable_rank_step
#check PlanarNikodym.Family.exists_analyticRankCover
#print axioms PlanarNikodym.Family.exists_analyticRankCover
#check PlanarNikodym.theorem_1_4_forward_proved
#print axioms PlanarNikodym.theorem_1_4_forward_proved
#check PlanarNikodym.Family.incidence_null_of_noNikodym_proved
#print axioms PlanarNikodym.Family.incidence_null_of_noNikodym_proved
#check PlanarNikodym.Family.exists_rankCover_localization
#print axioms PlanarNikodym.Family.exists_rankCover_localization
#check PlanarNikodym.exists_analytic_interval_sign_partition
#print axioms PlanarNikodym.exists_analytic_interval_sign_partition
#check PlanarNikodym.oneDimensional_analytic_sign_components
#print axioms PlanarNikodym.oneDimensional_analytic_sign_components
#check PlanarNikodym.exists_local_oneDimensional_analytic_separating_family
#print axioms PlanarNikodym.exists_local_oneDimensional_analytic_separating_family
#check PlanarNikodym.exists_local_oneDimensional_semianalytic_components
#print axioms PlanarNikodym.exists_local_oneDimensional_semianalytic_components
#check PlanarNikodym.oneDimensional_bounded_analytic_sign_components
#print axioms PlanarNikodym.oneDimensional_bounded_analytic_sign_components
#check PlanarNikodym.oneDimensional_bounded_analytic_sublevel_components
#print axioms PlanarNikodym.oneDimensional_bounded_analytic_sublevel_components
#check PlanarNikodym.exists_analytic_coordinate_quotient
#print axioms PlanarNikodym.exists_analytic_coordinate_quotient
#check PlanarNikodym.exists_analytic_graph_quotient
#print axioms PlanarNikodym.exists_analytic_graph_quotient
#check PlanarNikodym.exists_analytic_graph_factor
#print axioms PlanarNikodym.exists_analytic_graph_factor
#check PlanarNikodym.analytic_graph_factor_value
#print axioms PlanarNikodym.analytic_graph_factor_value
#check PlanarNikodym.exists_analytic_simple_root_preparation
#print axioms PlanarNikodym.exists_analytic_simple_root_preparation
#check PlanarNikodym.exists_analytic_simple_root_preparation_on
#print axioms PlanarNikodym.exists_analytic_simple_root_preparation_on
#check PlanarNikodym.exists_analytic_simple_root_division
#print axioms PlanarNikodym.exists_analytic_simple_root_division
#check PlanarNikodym.exists_analytic_monomial_division
#print axioms PlanarNikodym.exists_analytic_monomial_division
#check PlanarNikodym.exists_analytic_weierstrass_normalization_on
#print axioms PlanarNikodym.exists_analytic_weierstrass_normalization_on
#check PlanarNikodym.norm_changeOriginSeries_le_two_pow
#print axioms PlanarNikodym.norm_changeOriginSeries_le_two_pow
#check PlanarNikodym.analyticCoefficientSeries_radius_pos
#print axioms PlanarNikodym.analyticCoefficientSeries_radius_pos
#check PlanarNikodym.exists_analytic_coefficient_lift
#print axioms PlanarNikodym.exists_analytic_coefficient_lift
#check PlanarNikodym.coefficient_lift_eq_single_of_normalized_fiber
#print axioms PlanarNikodym.coefficient_lift_eq_single_of_normalized_fiber
#check PlanarNikodym.exists_weierstrass_banach_preparation
#print axioms PlanarNikodym.exists_weierstrass_banach_preparation
#check PlanarNikodym.exists_weierstrass_banach_division
#print axioms PlanarNikodym.exists_weierstrass_banach_division
#check PlanarNikodym.analyticAt_weierstrassSeriesEval
#print axioms PlanarNikodym.analyticAt_weierstrassSeriesEval
#check PlanarNikodym.weierstrassSeriesEval_preparation
#print axioms PlanarNikodym.weierstrassSeriesEval_preparation
#check PlanarNikodym.weierstrassSeriesEval_rescale
#print axioms PlanarNikodym.weierstrassSeriesEval_rescale
#check PlanarNikodym.exists_analytic_weierstrass_preparation
#print axioms PlanarNikodym.exists_analytic_weierstrass_preparation
#check PlanarNikodym.exists_analytic_weierstrass_preparation_on
#print axioms PlanarNikodym.exists_analytic_weierstrass_preparation_on
#check PlanarNikodym.exists_analytic_monic_polynomial_division
#print axioms PlanarNikodym.exists_analytic_monic_polynomial_division
#check PlanarNikodym.exists_analytic_weierstrass_division
#print axioms PlanarNikodym.exists_analytic_weierstrass_division
#check PlanarNikodym.exists_analytic_weierstrass_division_on
#print axioms PlanarNikodym.exists_analytic_weierstrass_division_on
#check PlanarNikodym.weierstrassPolynomial_finite_roots
#print axioms PlanarNikodym.weierstrassPolynomial_finite_roots
#check PlanarNikodym.exists_uniform_finite_analytic_fiber_zeros
#print axioms PlanarNikodym.exists_uniform_finite_analytic_fiber_zeros
#check PlanarNikodym.exists_uniform_finite_analytic_fiber_zeros_of_nonflat
#print axioms PlanarNikodym.exists_uniform_finite_analytic_fiber_zeros_of_nonflat
#check PlanarNikodym.analyticBandHomeomorph
#print axioms PlanarNikodym.analyticBandHomeomorph
#check PlanarNikodym.isConnected_analyticBand
#print axioms PlanarNikodym.isConnected_analyticBand
#check PlanarNikodym.Family.zero_auxiliary_null_cover
#print axioms PlanarNikodym.Family.zero_auxiliary_null_cover
#check PlanarNikodym.Family.zero_auxiliary_classification_proved
#print axioms PlanarNikodym.Family.zero_auxiliary_classification_proved
#check PlanarNikodym.theorem_1_4_zero_auxiliary_proved
#print axioms PlanarNikodym.theorem_1_4_zero_auxiliary_proved
#check PlanarNikodym.weierstrassDivisionOperator_eq_zero_of_scalar_identity
#print axioms PlanarNikodym.weierstrassDivisionOperator_eq_zero_of_scalar_identity
#check PlanarNikodym.eventually_weierstrassDivisionOperator_injective
#print axioms PlanarNikodym.eventually_weierstrassDivisionOperator_injective
#check PlanarNikodym.analytic_weierstrass_division_unique
#print axioms PlanarNikodym.analytic_weierstrass_division_unique
#check PlanarNikodym.exists_analytic_weierstrass_division_unique
#print axioms PlanarNikodym.exists_analytic_weierstrass_division_unique
#check PlanarNikodym.analytic_weierstrass_preparation_unique
#print axioms PlanarNikodym.analytic_weierstrass_preparation_unique
#check PlanarNikodym.exists_analytic_weierstrass_preparation_unique
#print axioms PlanarNikodym.exists_analytic_weierstrass_preparation_unique
#check PlanarNikodym.exists_uniform_finite_analytic_family_fiber_zeros
#print axioms PlanarNikodym.exists_uniform_finite_analytic_family_fiber_zeros
#check PlanarNikodym.exists_open_nhds_compact_fiber_property
#print axioms PlanarNikodym.exists_open_nhds_compact_fiber_property
#check PlanarNikodym.exists_open_nhds_compact_fiber_nonzero
#print axioms PlanarNikodym.exists_open_nhds_compact_fiber_nonzero
#check PlanarNikodym.finite_simple_analytic_fiber_zeros
#print axioms PlanarNikodym.finite_simple_analytic_fiber_zeros
#check PlanarNikodym.exists_ordered_analytic_simple_root_branches
#print axioms PlanarNikodym.exists_ordered_analytic_simple_root_branches
#check PlanarNikodym.analyticAt_polynomial_resultant
#print axioms PlanarNikodym.analyticAt_polynomial_resultant
#check PlanarNikodym.polynomial_no_common_root_of_resultant_ne_zero
#print axioms PlanarNikodym.polynomial_no_common_root_of_resultant_ne_zero
#check PlanarNikodym.analyticAt_weierstrassCollisionDet
#print axioms PlanarNikodym.analyticAt_weierstrassCollisionDet
#check PlanarNikodym.deriv_ne_zero_of_weierstrassCollisionDet_ne_zero
#print axioms PlanarNikodym.deriv_ne_zero_of_weierstrassCollisionDet_ne_zero
#check PlanarNikodym.analyticAt_weierstrassFamilyCollisionDet
#print axioms PlanarNikodym.analyticAt_weierstrassFamilyCollisionDet
#check PlanarNikodym.simple_disjoint_roots_of_weierstrassFamilyCollisionDet_ne_zero
#print axioms PlanarNikodym.simple_disjoint_roots_of_weierstrassFamilyCollisionDet_ne_zero
#check PlanarNikodym.weierstrassFamilyCollisionDet_eq_zero_of_collision
#print axioms PlanarNikodym.weierstrassFamilyCollisionDet_eq_zero_of_collision
#check PlanarNikodym.deriv_finset_product_ne_zero_of_simple_disjoint_roots
#print axioms PlanarNikodym.deriv_finset_product_ne_zero_of_simple_disjoint_roots
#check PlanarNikodym.exists_open_nhds_uniform_weierstrass_root_bound
#print axioms PlanarNikodym.exists_open_nhds_uniform_weierstrass_root_bound
#check PlanarNikodym.exists_ordered_analytic_polynomial_root_branches_of_collisionDet_ne_zero
#print axioms PlanarNikodym.exists_ordered_analytic_polynomial_root_branches_of_collisionDet_ne_zero
#check PlanarNikodym.exists_ordered_analytic_polynomial_family_root_branches
#print axioms PlanarNikodym.exists_ordered_analytic_polynomial_family_root_branches
#check PlanarNikodym.analytic_ordered_root_partition
#print axioms PlanarNikodym.analytic_ordered_root_partition
#check PlanarNikodym.ncard_range_analyticCylindricalCell
#print axioms PlanarNikodym.ncard_range_analyticCylindricalCell
#check PlanarNikodym.analyticGraphHomeomorph
#print axioms PlanarNikodym.analyticGraphHomeomorph
#check PlanarNikodym.finite_family_zero_or_nonzero_on_preconnected
#print axioms PlanarNikodym.finite_family_zero_or_nonzero_on_preconnected
#check PlanarNikodym.analyticCylindricalCell_separated_family_sign_constant
#print axioms PlanarNikodym.analyticCylindricalCell_separated_family_sign_constant
#check PlanarNikodym.exists_analytic_simple_root_cylindrical_partition
#print axioms PlanarNikodym.exists_analytic_simple_root_cylindrical_partition
#check PlanarNikodym.exists_analytic_polynomial_root_partition
#print axioms PlanarNikodym.exists_analytic_polynomial_root_partition
#check PlanarNikodym.exists_analytic_polynomial_family_root_partition
#print axioms PlanarNikodym.exists_analytic_polynomial_family_root_partition
#check PlanarNikodym.exists_analytic_polynomial_gcd_stratification
#print axioms PlanarNikodym.exists_analytic_polynomial_gcd_stratification
#check PlanarNikodym.exists_analytic_polynomial_squarefree_stratification
#print axioms PlanarNikodym.exists_analytic_polynomial_squarefree_stratification
#check PlanarNikodym.exists_analytic_polynomial_root_stratification
#print axioms PlanarNikodym.exists_analytic_polynomial_root_stratification
#check PlanarNikodym.exists_analytic_polynomial_multiplicity_reduction
#print axioms PlanarNikodym.exists_analytic_polynomial_multiplicity_reduction
#check PlanarNikodym.exists_global_ordered_analytic_polynomial_roots
#print axioms PlanarNikodym.exists_global_ordered_analytic_polynomial_roots
#check PlanarNikodym.exists_global_ordered_analytic_definable_polynomial_roots
#print axioms PlanarNikodym.exists_global_ordered_analytic_definable_polynomial_roots
#check PlanarNikodym.ranDefinableOn_polynomial_monic_division_coeff
#print axioms PlanarNikodym.ranDefinableOn_polynomial_monic_division_coeff
#check PlanarNikodym.ranDefinable_polynomialDegreeStratum
#print axioms PlanarNikodym.ranDefinable_polynomialDegreeStratum
#check PlanarNikodym.ranDefinableOn_orderedPolynomialRootBranch
#print axioms PlanarNikodym.ranDefinableOn_orderedPolynomialRootBranch
#check PlanarNikodym.analytic_critical_values_countable
#print axioms PlanarNikodym.analytic_critical_values_countable
#check PlanarNikodym.analytic_zero_differential_image_countable
#print axioms PlanarNikodym.analytic_zero_differential_image_countable
#check PlanarNikodym.compact_analytic_planar_critical_image_closed_null
#print axioms PlanarNikodym.compact_analytic_planar_critical_image_closed_null
#check PlanarNikodym.compact_analytic_critical_center_image_closed_null
#print axioms PlanarNikodym.compact_analytic_critical_center_image_closed_null
#check PlanarNikodym.closure_analytic_critical_center_image_null
#print axioms PlanarNikodym.closure_analytic_critical_center_image_null
#check PlanarNikodym.analytic_planar_critical_image_null
#print axioms PlanarNikodym.analytic_planar_critical_image_null
#check PlanarNikodym.compact_analytic_parameter_critical_centers_closed_null
#print axioms PlanarNikodym.compact_analytic_parameter_critical_centers_closed_null
#check PlanarNikodym.exists_analytic_polynomial_family_root_stratification
#print axioms PlanarNikodym.exists_analytic_polynomial_family_root_stratification
#check PlanarNikodym.polynomialThomFamilyCell_ordConnected
#print axioms PlanarNikodym.polynomialThomFamilyCell_ordConnected
#check PlanarNikodym.polynomialThomFamilyCell_closure
#print axioms PlanarNikodym.polynomialThomFamilyCell_closure
#check PlanarNikodym.polynomial_derivative_closed_separating_family
#print axioms PlanarNikodym.polynomial_derivative_closed_separating_family
#check PlanarNikodym.polynomialThomFamilyCell_closure_union
#print axioms PlanarNikodym.polynomialThomFamilyCell_closure_union
#check PlanarNikodym.polynomialThomCode_injective_on_roots
#print axioms PlanarNikodym.polynomialThomCode_injective_on_roots
#check PlanarNikodym.continuousOn_polynomialThomRoot
#print axioms PlanarNikodym.continuousOn_polynomialThomRoot
#check PlanarNikodym.finite_continuous_definable_polynomial_root_partition
#print axioms PlanarNikodym.finite_continuous_definable_polynomial_root_partition
#check PlanarNikodym.exists_local_analytic_thom_root_partition
#print axioms PlanarNikodym.exists_local_analytic_thom_root_partition
#check PlanarNikodym.exists_common_analytic_fraction_gcd_stratification
#print axioms PlanarNikodym.exists_common_analytic_fraction_gcd_stratification
#check PlanarNikodym.exists_common_analytic_polynomial_gcd_stratification
#print axioms PlanarNikodym.exists_common_analytic_polynomial_gcd_stratification
#check PlanarNikodym.CommonAnalyticPolynomialGcdStratification.exists_common_analytic_tests
#print axioms PlanarNikodym.CommonAnalyticPolynomialGcdStratification.exists_common_analytic_tests
#check PlanarNikodym.exists_common_analytic_fraction_squarefree_stratification
#print axioms PlanarNikodym.exists_common_analytic_fraction_squarefree_stratification
#check PlanarNikodym.exists_common_analytic_simple_squarefree_stratification
#print axioms PlanarNikodym.exists_common_analytic_simple_squarefree_stratification
#check PlanarNikodym.exists_common_analytic_polynomial_root_tests
#print axioms PlanarNikodym.exists_common_analytic_polynomial_root_tests
#check PlanarNikodym.exists_common_analytic_polynomial_family_root_tests
#print axioms PlanarNikodym.exists_common_analytic_polynomial_family_root_tests
#check PlanarNikodym.continuous_selector_eq_on_preconnected
#print axioms PlanarNikodym.continuous_selector_eq_on_preconnected
#check PlanarNikodym.exists_fixed_continuous_root_ownership
#print axioms PlanarNikodym.exists_fixed_continuous_root_ownership
#check PlanarNikodym.exists_common_analytic_polynomial_cylindrical_tests
#print axioms PlanarNikodym.exists_common_analytic_polynomial_cylindrical_tests
#check PlanarNikodym.exists_local_analytic_polynomial_cylindrical_tests
#print axioms PlanarNikodym.exists_local_analytic_polynomial_cylindrical_tests
#check PlanarNikodym.linearIntervalSignCell_closure
#print axioms PlanarNikodym.linearIntervalSignCell_closure
#check PlanarNikodym.exists_local_oneDimensional_analytic_separating_family_with_frontier
#print axioms PlanarNikodym.exists_local_oneDimensional_analytic_separating_family_with_frontier
#check PlanarNikodym.exists_common_nonflat_analytic_direction
#print axioms PlanarNikodym.exists_common_nonflat_analytic_direction
#check PlanarNikodym.exists_common_finite_analytic_line_orders
#print axioms PlanarNikodym.exists_common_finite_analytic_line_orders
#check PlanarNikodym.exists_real_nonzero_direction_frame
#print axioms PlanarNikodym.exists_real_nonzero_direction_frame
#check PlanarNikodym.exists_finite_family_weierstrass_frame
#print axioms PlanarNikodym.exists_finite_family_weierstrass_frame
#check PlanarNikodym.exists_finite_analytic_germ_preparation
#print axioms PlanarNikodym.exists_finite_analytic_germ_preparation
#check PlanarNikodym.weierstrass_iterated_derivative_normalization
#print axioms PlanarNikodym.weierstrass_iterated_derivative_normalization
#check PlanarNikodym.exists_local_analytic_derivative_thom_tests
#print axioms PlanarNikodym.exists_local_analytic_derivative_thom_tests
#check PlanarNikodym.exists_fixedStrip_analytic_derivative_thom_tests
#print axioms PlanarNikodym.exists_fixedStrip_analytic_derivative_thom_tests
#check PlanarNikodym.exists_polynomial_connected_refinement_lifting
#print axioms PlanarNikodym.exists_polynomial_connected_refinement_lifting
#check PlanarNikodym.analyticDerivativeThomCylinder_closure
#print axioms PlanarNikodym.analyticDerivativeThomCylinder_closure
#check PlanarNikodym.analyticDerivativeCylindricalSignCell_closure
#print axioms PlanarNikodym.analyticDerivativeCylindricalSignCell_closure
#check PlanarNikodym.analyticStrongSignCell_sum_connected_or_empty
#print axioms PlanarNikodym.analyticStrongSignCell_sum_connected_or_empty
#check PlanarNikodym.exists_local_analytic_sign_refinement_affine
#print axioms PlanarNikodym.exists_local_analytic_sign_refinement_affine
#check PlanarNikodym.Family.smooth_dyadicMaximalEstimate_proved_e2
#print axioms PlanarNikodym.Family.smooth_dyadicMaximalEstimate_proved_e2
#check PlanarNikodym.Family.local_smooth_Lp_extension_of_geometric_endpoint_e2
#print axioms PlanarNikodym.Family.local_smooth_Lp_extension_of_geometric_endpoint_e2
#check PlanarNikodym.Family.compact_intervalMaximal_e2_Lp_of_geometric_on_open
#print axioms PlanarNikodym.Family.compact_intervalMaximal_e2_Lp_of_geometric_on_open
#check PlanarNikodym.Family.exists_intervalMaximal_Lp_extension_e2
#print axioms PlanarNikodym.Family.exists_intervalMaximal_Lp_extension_e2
#check PlanarNikodym.Family.intervalMaximal_Lp_extension_unique_e2
#print axioms PlanarNikodym.Family.intervalMaximal_Lp_extension_unique_e2
#check PlanarNikodym.Family.e3_jetSmoothingInput_of_cinematic_support
#print axioms PlanarNikodym.Family.e3_jetSmoothingInput_of_cinematic_support
#check PlanarNikodym.Family.e3_jetSmoothingInput_of_smooth_on_open
#print axioms PlanarNikodym.Family.e3_jetSmoothingInput_of_smooth_on_open
#check PlanarNikodym.Family.e3_timeIncidence_null_of_isSmooth
#print axioms PlanarNikodym.Family.e3_timeIncidence_null_of_isSmooth
#check PlanarNikodym.corollary_1_2_smooth
#print axioms PlanarNikodym.corollary_1_2_smooth
#check PlanarNikodym.localAnalyticConnectedRefinement_fin
#print axioms PlanarNikodym.localAnalyticConnectedRefinement_fin
#check PlanarNikodym.localAnalyticSeparatingFrontier_fin
#print axioms PlanarNikodym.localAnalyticSeparatingFrontier_fin
#check PlanarNikodym.exists_fixedStrip_thom_frontier_tests
#print axioms PlanarNikodym.exists_fixedStrip_thom_frontier_tests
#check PlanarNikodym.exists_local_finite_analytic_sign_components
#print axioms PlanarNikodym.exists_local_finite_analytic_sign_components
#check PlanarNikodym.LocallySemianalytic.locallyFinite_components
#print axioms PlanarNikodym.LocallySemianalytic.locallyFinite_components
#check PlanarNikodym.LocallySemianalytic.sUnion_components
#print axioms PlanarNikodym.LocallySemianalytic.sUnion_components
#check PlanarNikodym.LocallySemianalytic.connectedComponentIn
#print axioms PlanarNikodym.LocallySemianalytic.connectedComponentIn
#check PlanarNikodym.LocallySemianalytic.components_finite_of_bounded
#print axioms PlanarNikodym.LocallySemianalytic.components_finite_of_bounded
#check PlanarNikodym.localAnalyticDimensionedRefinement_fin
#check PlanarNikodym.exists_local_finite_analytic_chart_stratification
#check PlanarNikodym.LocallySemianalytic.finite_definable_components_of_bounded
#check PlanarNikodym.Family.ranTame_components_seed
#check PlanarNikodym.restrictedAnalyticTerm_piecewiseAnalyticAt
#check PlanarNikodym.restrictedAnalyticQF_locallySemianalytic
#check PlanarNikodym.restrictedAnalyticQF_bounded_exists_components
#check PlanarNikodym.LocallySemianalytic.critical_image_closure_definable_closed_null
#check PlanarNikodym.e2_exists_contDiff_extension_closed_product_with_jets
#check PlanarNikodym.Family.cinematicMatrixWithin_e2_eq_ambient
#check PlanarNikodym.Family.exists_compact_closed_smooth_extension_e2
#check PlanarNikodym.Family.compact_intervalMaximal_e2_Lp_of_closed_smooth_within_cinematic
#check PlanarNikodym.Family.compact_intervalMaximal_e2_Lp_of_closed_smooth_ambient_jets
#print axioms PlanarNikodym.localAnalyticDimensionedRefinement_fin
#print axioms PlanarNikodym.exists_local_finite_analytic_chart_stratification
#print axioms PlanarNikodym.Family.ranTame_components_seed
#print axioms PlanarNikodym.restrictedAnalyticQF_bounded_exists_components
#print axioms PlanarNikodym.LocallySemianalytic.critical_image_closure_definable_closed_null
#print axioms PlanarNikodym.e2_exists_contDiff_extension_closed_product_with_jets
#print axioms PlanarNikodym.Family.cinematicMatrixWithin_e2_eq_ambient
#print axioms PlanarNikodym.Family.compact_intervalMaximal_e2_Lp_of_closed_smooth_within_cinematic
#check PlanarNikodym.localAnalyticClosedWindowRefinement_fin
#check PlanarNikodym.exists_local_finite_semianalytic_stratification
#check PlanarNikodym.LocallySemianalytic.closure
#check PlanarNikodym.LocallySemianalytic.frontier
#check PlanarNikodym.LocallySemianalytic.exists_finite_analytic_chart_cover
#check PlanarNikodym.AnalyticStratificationChart.dimH_image_le
#check PlanarNikodym.exists_local_semianalytic_strata_with_closed_null_projection_exception
#print axioms PlanarNikodym.localAnalyticClosedWindowRefinement_fin
#print axioms PlanarNikodym.exists_local_finite_semianalytic_stratification
#print axioms PlanarNikodym.LocallySemianalytic.closure
#print axioms PlanarNikodym.LocallySemianalytic.exists_finite_analytic_chart_cover
#print axioms PlanarNikodym.exists_local_semianalytic_strata_with_closed_null_projection_exception
#check PlanarNikodym.e2_positive_kernel_bilinear_schur
#check PlanarNikodym.e2_exists_uniform_local_gradient_separation
#check PlanarNikodym.e2FIONormalizedDifference_contDiff
#print axioms PlanarNikodym.e2_positive_kernel_bilinear_schur
#print axioms PlanarNikodym.e2_exists_uniform_local_gradient_separation
#print axioms PlanarNikodym.e2FIONormalizedDifference_contDiff
#check PlanarNikodym.AnalyticStratificationChart.dimH_image
#check PlanarNikodym.AnalyticStratificationChart.dim_eq_of_image_eq
#check PlanarNikodym.stratum_relative_closure_dimH
#check PlanarNikodym.LocallySemianalytic.dimH_closure
#check PlanarNikodym.LocallySemianalytic.dimH_missing_boundary_le
#check PlanarNikodym.LocallySemianalytic.isClosed_of_dimH_zero
#check PlanarNikodym.exists_center_ordered_stratum_chart
#check PlanarNikodym.exists_center_ordered_analytic_piece
#check PlanarNikodym.exists_finite_center_ordered_analytic_piece_cover
#check PlanarNikodym.e2FullFIOIntegral_gram_energy_of_continuous_amplitude
#check PlanarNikodym.e2_exists_uniform_two_dimensional_nonstationary_decay
#print axioms PlanarNikodym.AnalyticStratificationChart.dimH_image
#print axioms PlanarNikodym.LocallySemianalytic.dimH_closure
#print axioms PlanarNikodym.LocallySemianalytic.dimH_missing_boundary_le
#print axioms PlanarNikodym.exists_center_ordered_analytic_piece
#print axioms PlanarNikodym.exists_finite_center_ordered_analytic_piece_cover
#print axioms PlanarNikodym.e2FullFIOIntegral_gram_energy_of_continuous_amplitude
#print axioms PlanarNikodym.e2_exists_uniform_two_dimensional_nonstationary_decay
#check PlanarNikodym.Family.e2SelectedPhaseGradient_fderiv_isInvertible
#print axioms PlanarNikodym.Family.e2SelectedPhaseGradient_fderiv_isInvertible
#check PlanarNikodym.Family.exists_e2_cinematic_gradient_separation
#print axioms PlanarNikodym.Family.exists_e2_cinematic_gradient_separation
#check PlanarNikodym.Family.exists_e2_actual_phase_gradient_separation
#print axioms PlanarNikodym.Family.exists_e2_actual_phase_gradient_separation
#check PlanarNikodym.e2_exists_exact_normalized_gram_amplitude
#print axioms PlanarNikodym.e2_exists_exact_normalized_gram_amplitude
#check PlanarNikodym.e2_normalized_gradient_lower_bound
#print axioms PlanarNikodym.e2_normalized_gradient_lower_bound
#check PlanarNikodym.e2_exists_local_gram_offDiagonal_decay
#print axioms PlanarNikodym.e2_exists_local_gram_offDiagonal_decay
#check PlanarNikodym.e2_exists_local_gram_polynomial_decay
#print axioms PlanarNikodym.e2_exists_local_gram_polynomial_decay
#check PlanarNikodym.e2_plane_weight_bilinear_schur
#print axioms PlanarNikodym.e2_plane_weight_bilinear_schur
#check PlanarNikodym.e2_exists_local_full_fio_energy_bound
#print axioms PlanarNikodym.e2_exists_local_full_fio_energy_bound
#check PlanarNikodym.e2_exists_local_full_fio_L2_bound
#print axioms PlanarNikodym.e2_exists_local_full_fio_L2_bound
#check PlanarNikodym.Family.Foliations.countableUnion
#check PlanarNikodym.Family.covered_countableUnion
#check PlanarNikodym.Family.rankPieceRemainder
#check PlanarNikodym.Family.rankPieceClosureCenters
#check PlanarNikodym.Family.rankPieceClosureCenters_null_of_closed_exception
#check PlanarNikodym.Family.locallyReusedCovered_of_countable_rankPieces_strong
#check PlanarNikodym.Family.null_cover_of_countable_rankPieces_proved
#check PlanarNikodym.Family.classification_of_countable_rankPieces_proved
#check PlanarNikodym.RankDecomposition.rankPieceClosureCenters_null
#check PlanarNikodym.OpenParameterCover.null_cover_of_controlled_rankPieces
#check PlanarNikodym.OpenParameterCover.classification_of_controlled_rankPieces
#check PlanarNikodym.theorem_1_4_of_bounded_controlled_rankPieces
#print axioms PlanarNikodym.Family.locallyReusedCovered_of_countable_rankPieces_strong
#print axioms PlanarNikodym.Family.classification_of_countable_rankPieces_proved
#print axioms PlanarNikodym.RankDecomposition.rankPieceClosureCenters_null
#print axioms PlanarNikodym.theorem_1_4_of_bounded_controlled_rankPieces
#check PlanarNikodym.exists_regular_thom_derivative
#check PlanarNikodym.regular_equations_polynomial_thom_cell
#check PlanarNikodym.localAnalyticRegularRefinement_fin
#check PlanarNikodym.exists_local_finite_regular_semianalytic_stratification
#check PlanarNikodym.AnalyticStratificationChart.regular_equations_tangent
#check PlanarNikodym.LocallySemianalytic.exists_finite_regular_analytic_chart_cover
#check PlanarNikodym.finrank_restricted_range_eq_stacked_sub
#check PlanarNikodym.exists_finiteEvaluation_all_restricted_ranks
#check PlanarNikodym.exists_finiteEvaluation_stacked_rank_formulas
#check PlanarNikodym.vertical_range_eq_tangent_inf_ker
#check PlanarNikodym.AnalyticPiece.ranks_eq_intrinsic
#check PlanarNikodym.AnalyticStratificationChart.exists_generic_intrinsic_ranks
#check PlanarNikodym.chart_dim_lt_of_subset_missing_boundary
#check PlanarNikodym.LocallySemianalytic.exists_finite_intrinsic_rank_chart_cover
#check PlanarNikodym.LocallySemianalytic.exists_finite_function_intrinsic_rank_cover
#check PlanarNikodym.Family.exists_finite_intrinsic_rank_cover
#check PlanarNikodym.Family.exists_finite_intrinsic_rank_ball_cover
#print axioms PlanarNikodym.localAnalyticRegularRefinement_fin
#print axioms PlanarNikodym.exists_local_finite_regular_semianalytic_stratification
#print axioms PlanarNikodym.AnalyticStratificationChart.regular_equations_tangent
#print axioms PlanarNikodym.exists_finiteEvaluation_stacked_rank_formulas
#print axioms PlanarNikodym.AnalyticPiece.ranks_eq_intrinsic
#print axioms PlanarNikodym.LocallySemianalytic.exists_finite_intrinsic_rank_chart_cover
#print axioms PlanarNikodym.Family.exists_finite_intrinsic_rank_ball_cover
#check PlanarNikodym.exists_analytic_sign_piece_barrier
#check PlanarNikodym.exists_positive_fiber_maximum
#check PlanarNikodym.exists_positive_barrier_tilt
#check PlanarNikodym.exists_analytic_regular_level_chart
#check PlanarNikodym.analytic_rank_one_fiber_maximum_derivative
#check PlanarNikodym.AnalyticStratificationChart.rank_one_fiber_extremum
#check PlanarNikodym.AnalyticStratificationChart.exists_fiber_critical_minor
#check PlanarNikodym.AnalyticStratificationChart.rank_one_fiber_cutting_step
#check PlanarNikodym.LocallySemianalytic.exists_finite_barrier_cover
#check PlanarNikodym.AnalyticStratificationChart.exists_semianalytic_fiber_cut
#check PlanarNikodym.AnalyticStratificationChart.critical_projection_compact_null
#check PlanarNikodym.finite_intrinsic_rank_critical_fiber_cut
#check PlanarNikodym.finite_intrinsic_rank_critical_centers_compact_null
#check PlanarNikodym.finite_intrinsic_rank_critical_source_closure_projection_null
#check PlanarNikodym.Family.exists_intrinsic_rank_ball_cover_with_critical_exception
#print axioms PlanarNikodym.LocallySemianalytic.exists_finite_barrier_cover
#print axioms PlanarNikodym.AnalyticStratificationChart.exists_semianalytic_fiber_cut
#print axioms PlanarNikodym.AnalyticStratificationChart.critical_projection_compact_null
#print axioms PlanarNikodym.finite_intrinsic_rank_critical_source_closure_projection_null
#print axioms PlanarNikodym.Family.exists_intrinsic_rank_ball_cover_with_critical_exception
#check PlanarNikodym.AnalyticStratificationChart.range_fderiv_eq_of_immersion_subset
#check PlanarNikodym.AnalyticPiece.ranks_eq_coordinate_intrinsic
#check PlanarNikodym.IntrinsicRankChart.exists_center_rankPiece
#check PlanarNikodym.IntrinsicRankChart.exists_countable_center_rankPiece_cover
#check PlanarNikodym.Family.exists_controlled_rank_cover_on_semianalytic_source
#check PlanarNikodym.Family.exists_controlled_rank_cover_on_coordinate_ball
#check PlanarNikodym.CoordinateBallParameterCover.exists_controlled_rank_pieces
#check PlanarNikodym.Family.general_null_cover_proved
#check PlanarNikodym.Family.general_classification_proved
#check PlanarNikodym.theorem_1_4_proved
#check PlanarNikodym.Family.exists_finite_rank_witnesses
#check PlanarNikodym.Proposition16PaperStatement
#check PlanarNikodym.proposition_1_6_paper_proved
#print axioms PlanarNikodym.AnalyticPiece.ranks_eq_coordinate_intrinsic
#print axioms PlanarNikodym.IntrinsicRankChart.exists_center_rankPiece
#print axioms PlanarNikodym.Family.exists_controlled_rank_cover_on_coordinate_ball
#print axioms PlanarNikodym.Family.general_null_cover_proved
#print axioms PlanarNikodym.Family.general_classification_proved
#print axioms PlanarNikodym.theorem_1_4_proved
#print axioms PlanarNikodym.Family.exists_finite_rank_witnesses
#print axioms PlanarNikodym.proposition_1_6_paper_proved
#check PlanarNikodym.RankDecomposition.center_image_volume_lt_top
#check PlanarNikodym.Family.not_rankDecomposition_of_infinite_center_volume
#check PlanarNikodym.Family.not_rankDecomposition_of_univ_domain
#check PlanarNikodym.finite_intrinsic_rank_critical_component_sources
#check PlanarNikodym.Family.exists_rankDecomposition_of_finite_open_regions
#check PlanarNikodym.IntrinsicRankChart.full_dimensional_image_open
#check PlanarNikodym.IntrinsicRankChart.constant_ranks_on_full_dimensional_image
#check PlanarNikodym.LocallySemianalytic.planar_open_frontier_projection_compact_null
#check PlanarNikodym.Family.exists_zero_auxiliary_rankDecomposition_of_finite_open_cover
#check PlanarNikodym.Family.exists_zero_auxiliary_finite_rankDecomposition_on_source
#check PlanarNikodym.Family.exists_zero_auxiliary_finite_rankDecomposition
#check PlanarNikodym.Family.exists_zero_auxiliary_finite_rankDecomposition_seed
#check PlanarNikodym.proposition_1_6_strong_zero_auxiliary_proved
#check PlanarNikodym.Family.isOpen_analyticParameterNeighborhood
#check PlanarNikodym.Family.closure_subset_analyticParameterNeighborhood
#check PlanarNikodym.Family.isAnalytic_on_analyticParameterNeighborhood
#check PlanarNikodym.image_sUnion_components_meeting_target_component
#check PlanarNikodym.LocallySemianalytic.exists_component_image_source
#check PlanarNikodym.LocallySemianalytic.exists_component_image_source_with_closure
#check PlanarNikodym.finiteOpenDisjointPatch_subset
#check PlanarNikodym.finiteOpenDisjointPatch_isOpen
#check PlanarNikodym.finiteOpenDisjointPatch_pairwise
#check PlanarNikodym.finiteOpenDisjointPatch_cover
#check PlanarNikodym.LocallySemianalytic.finiteOpenDisjointPatch
#check PlanarNikodym.AnalyticStratificationChart.derivative_surjective_of_dim_eq
#check PlanarNikodym.AnalyticStratificationChart.isOpen_image_of_dim_eq
#check PlanarNikodym.Family.ranTame_components_of_semianalytic_image
#check PlanarNikodym.Family.ranTame_components_of_analytic_image
#check PlanarNikodym.locallySemianalytic_parameterFrame_ball
#check PlanarNikodym.Family.analyticParameterDomain_semianalytic
#print axioms PlanarNikodym.LocallySemianalytic.exists_component_image_source_with_closure
#print axioms PlanarNikodym.finite_intrinsic_rank_critical_component_sources
#print axioms PlanarNikodym.Family.ranTame_components_of_semianalytic_image
#print axioms PlanarNikodym.Family.exists_zero_auxiliary_finite_rankDecomposition_on_source
#print axioms PlanarNikodym.Family.exists_zero_auxiliary_finite_rankDecomposition_seed
#print axioms PlanarNikodym.proposition_1_6_strong_zero_auxiliary_proved
#print axioms PlanarNikodym.Family.not_rankDecomposition_of_univ_domain
#check PlanarNikodym.continuous_partialFourierData_of_compact
#check PlanarNikodym.continuous_weightedPartialFourierData
#check PlanarNikodym.partialDataAmplitude_tsupport_subset
#check PlanarNikodym.Family.cutoffPartialExtension_eq_fullFIO
#check PlanarNikodym.cinematic_partial_L2_scaling
#check PlanarNikodym.Family.exists_cinematic_partial_main_L2
#check PlanarNikodym.Family.exists_smooth_positive_main_global_smoothing
#check PlanarNikodym.Family.exists_smooth_two_sided_main_global_smoothing
#check PlanarNikodym.Family.exists_smooth_finite_cinematic_small_main_Lp_norm_partition
#check PlanarNikodym.Family.exists_smooth_full_cinematic_small_main_Lp
#check PlanarNikodym.Family.exists_smooth_full_cinematic_linear_scale_main_Lp
#check PlanarNikodym.Family.exists_smooth_finite_cinematic_small_main_L2_norm_partition
#check PlanarNikodym.Family.exists_smooth_finite_cinematic_small_main_Lp_partition
#check PlanarNikodym.Family.exists_smooth_zero_dim_positive_main_eLp_smoothing
#check PlanarNikodym.Family.exists_smooth_zero_dim_positive_main_eLp_smoothing_nat
#check PlanarNikodym.Family.exists_smooth_zero_dim_positive_main_smoothing
#check PlanarNikodym.Family.exists_cinematic_scalar_weighted_L2
#check PlanarNikodym.Family.exists_cinematic_scalar_weighted_dyadic_L2
#check PlanarNikodym.Family.exists_smooth_jet_smoothing_neighborhood
#check PlanarNikodym.Family.smooth_jetSmoothingInput_of_cinematic_support
#check PlanarNikodym.Family.theorem_2_1_smooth_of_contDiff
#check PlanarNikodym.Family.exists_smooth_nonnegative_centered_scalar_weighted_smoothing
#check PlanarNikodym.Family.exists_smooth_nonnegative_scalar_weighted_smoothing
#check PlanarNikodym.Family.exists_smooth_scalar_weighted_smoothing_on_open
#check PlanarNikodym.Family.exists_smooth_scalar_weighted_smoothing_neighborhood
#check PlanarNikodym.planeAuxEquiv
#check PlanarNikodym.planeAuxEquiv_zero
#check PlanarNikodym.planeAuxEquiv_direction
#check PlanarNikodym.planeAuxEquiv_measurePreserving
#check PlanarNikodym.Family.selectedPlanePhase
#check PlanarNikodym.Family.selectedPlanePhase_contDiff
#check PlanarNikodym.Family.selectedPlanePhase_gradient
#check PlanarNikodym.Family.selectedPlanePatch
#check PlanarNikodym.Family.exists_selectedPlane_phase_separation
#check PlanarNikodym.cinematicRetainedCoordinates
#check PlanarNikodym.cinematicRetainedCoordinates_volume_preserving
#check PlanarNikodym.Family.retainedCinematicPhase
#check PlanarNikodym.Family.retainedCinematicPhase_contDiff
#check PlanarNikodym.Family.retainedCinematicPhase_gradient
#check PlanarNikodym.Family.exists_local_cinematic_full_fio_L2_bound
#check PlanarNikodym.exists_finite_complex_amplitude_partition
#check PlanarNikodym.stronglyMeasurable_fullFIO_of_continuous
#check PlanarNikodym.integrable_fullFIO_input_of_continuous
#check PlanarNikodym.Family.exists_cinematic_full_fio_L2_bound
#check PlanarNikodym.Family.one_auxiliary_summable_dyadic_estimate
#check PlanarNikodym.Family.one_auxiliary_cutoff_Lp_extension
#check PlanarNikodym.Family.one_auxiliary_jet_L2_proved
#check PlanarNikodym.Family.one_auxiliary_band_maximal_L2_proved
#check PlanarNikodym.Family.one_auxiliary_compact_maximal_bound
#check PlanarNikodym.Family.one_auxiliary_compact_maximal_Lp_extension
#check PlanarNikodym.Family.theorem_1_1_one_auxiliary_proved
#check PlanarNikodym.Family.theorem_1_1_one_auxiliary_ambient_jets
#check PlanarNikodym.retainedFIOCoordinateEquiv
#check PlanarNikodym.exists_retained_full_gram_offDiagonal_decay
#check PlanarNikodym.exists_retained_uniform_gram_kernel_bound
#check PlanarNikodym.full_fio_energy_of_gram_bound
#check PlanarNikodym.exists_retained_gram_polynomial_decay
#check PlanarNikodym.exists_retained_full_fio_energy_bound
#check PlanarNikodym.exists_retained_full_fio_L2_bound
#check PlanarNikodym.Family.smooth_high_p_summable_dyadic_estimate
#check PlanarNikodym.Family.smooth_high_p_compact_maximal_bound
#check PlanarNikodym.Family.smooth_high_p_compact_maximal_Lp_extension
#check PlanarNikodym.Family.theorem_1_1_high_p_proved
#check PlanarNikodym.Family.theorem_1_1_high_p_ambient_jets
#check PlanarNikodym.Family.exists_smooth_local_smoothing
#check PlanarNikodym.Family.theorem_2_1_smooth_proved
#check PlanarNikodym.Family.corollary_2_2_smooth_proved
#print axioms PlanarNikodym.Family.theorem_2_1_smooth_proved
#print axioms PlanarNikodym.Family.corollary_2_2_smooth_proved
#print axioms PlanarNikodym.Family.exists_cinematic_partial_main_L2
#print axioms PlanarNikodym.Family.one_auxiliary_band_maximal_L2_proved
#print axioms PlanarNikodym.Family.theorem_1_1_one_auxiliary_proved
#print axioms PlanarNikodym.Family.theorem_1_1_high_p_proved
