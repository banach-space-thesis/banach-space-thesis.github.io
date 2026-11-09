import SurveyStatements.P5OperatorReductionFiniteSelection
import SurveyStatements.P5OperatorReductionOneSidedMoments
import SurveyStatements.P5OperatorReductionShadowMomentLimits
import SurveyStatements.P5OperatorReductionSignRestriction
import SurveyStatements.P5OperatorReductionTraceSelectionMoments
import SurveyStatements.P5OperatorReductionOneSidedTraceMoments
import SurveyStatements.P5OperatorReductionCandidateSplits
import SurveyStatements.P5OperatorReductionConcreteErrorListsAudit
import SurveyStatements.P5OperatorReductionTraceNormalization
import SurveyStatements.P5OperatorReductionBackwardMoments
import SurveyStatements.P5OperatorReductionNormalizedTraceBalances
import Lean

open Lean Elab Command
run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements.P5OperatorReduction).isPrefixOf name ||
    (`SurveyStatements.P5Support).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved finite selection/moment axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} finite selection/moment declarations without admissions."

#print axioms SurveyStatements.P5OperatorReduction.exists_refined_split_of_finite_moment_limits
#print axioms SurveyStatements.P5OperatorReduction.functional_signedBlock_family_moments_eventually_small
#print axioms SurveyStatements.P5OperatorReduction.limiting_restricted_reader_signed_variance_small
#print axioms SurveyStatements.P5OperatorReduction.mean_sign_restrict_packet
#print axioms SurveyStatements.P5OperatorReduction.registered_trace_split_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.limiting_functional_signedBlock_second_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.exists_candidate_split_of_actual_error_moment_limits
#print axioms SurveyStatements.P5OperatorReduction.candidate_blockReader_second_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.normalized_registered_trace_balance_moment_tendsto_zero
