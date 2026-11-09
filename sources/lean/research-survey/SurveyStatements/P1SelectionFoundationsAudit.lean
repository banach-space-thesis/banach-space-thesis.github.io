import SurveyStatements.P1WeakNullDualClusters
import SurveyStatements.P1WeakCauchyBasic
import SurveyStatements.P1PrefixClassRamsey
import SurveyStatements.P1DifferenceSummation
import SurveyStatements.P1ConstantSuppression
import SurveyStatements.P1FiniteWitnessSelection
import SurveyStatements.P1PhaseSectorEstimate
import SurveyStatements.P1PhaseSectors
import SurveyStatements.P1WitnessMassTrim
import SurveyStatements.P1FiniteCoefficientTails
import SurveyStatements.P1SuppressionCrossEvaluation
import SurveyStatements.P1SuppressionWitnessColors
import SurveyStatements.P1SuppressionRestriction
import SurveyStatements.P1MatchingColors
import SurveyStatements.P1TwoFrontInfinite
import SurveyStatements.P1MatchingIntersection
import SurveyStatements.P1MatchingResiduals
import SurveyStatements.P1MatchingOrder
import SurveyStatements.P1SuppressionAssignmentContradiction
import SurveyStatements.P1WeakCauchySuppressionSeparation
import Lean

set_option maxHeartbeats 800000

/-! No admission exception is allowed for the remaining-selection support
graph. This module deliberately does not import the unfinished main. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in P1 selection foundations: {axiomName}"
  logInfo m!"Audited {declarations.length} selection-support declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P1.bidual_annihilator_kernel_norms
#print axioms SurveyStatements.P1.nontrivial_weakCauchy_kernel_norms
#print axioms SurveyStatements.P1.finite_kernel_norming_family
#print axioms SurveyStatements.P1.kernel_norming_uniform_prefix_bound
#print axioms SurveyStatements.P1.normalized_kernelNull_exists_basic_subsequence
#print axioms SurveyStatements.P1.nontrivial_weakCauchy_exists_basic_subsequence
#print axioms SurveyStatements.P1.prefixClass_closedRamsey
#print axioms SurveyStatements.P1.prefixClass_finiteColorRamsey
#print axioms SurveyStatements.P1.stronglySumming_difference_coefficients_converge
#print axioms SurveyStatements.P1.finite_complex_subsetSum_cube_bound
#print axioms SurveyStatements.P1.exists_c0_embedding_of_finite_coefficient_bounds
#print axioms SurveyStatements.P1.unitModulusSuppression_toroidal_elton_odell
#print axioms SurveyStatements.P1.exists_locally_constant_finiteWitness_selection
#print axioms SurveyStatements.P1.matched_phase_sector_realPart_bound
#print axioms SurveyStatements.P1.finiteSet_matching_lemma
#print axioms SurveyStatements.P1.exists_complex_phase_sector_witness
#print axioms SurveyStatements.P1.weakNull_boundedDual_coordinate_cluster
#print axioms SurveyStatements.P1.finite_weighted_tail_trim
#print axioms SurveyStatements.P1.exists_unitSuppressionWitness_of_failure
#print axioms SurveyStatements.P1.matched_unitSuppressionWitness_contradiction
#print axioms SurveyStatements.P1.unitSuppressionWitness_assignment_contradiction
#print axioms SurveyStatements.P1.weakNull_exists_unitModulusSuppressionOn
#print axioms SurveyStatements.P1.normalized_weakNull_toroidal_elton_odell
#print axioms SurveyStatements.P1.nontrivial_weakCauchy_toroidal_elton_odell
