import SurveyStatements.P5OperatorReductionPacketMatrixRaw
import Lean

set_option maxHeartbeats 1000000
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
      throwError "Unapproved axiom in genuine normalized packet matrix: {axiomName}"
  logInfo m!"Audited {declarations.length} normalized packet-matrix declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_row_sum_le
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_offDiagonalSquareSum_le
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_variance_le_power
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_variance_uniform_small
#print axioms SurveyStatements.P5OperatorReduction.packetMatrix_refine_card
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_refinement_variance_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_exists_refinement_small
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_eq_raw
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrixVariance_eq_raw
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_variance_uniform_small_norm_bound
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_refinement_family_sum_eventually_small
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_exists_refinement_family_sum_small
