import SurveyStatements.P5OperatorReductionInnerMatrixVariance
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5OperatorReduction.innerMatrixNormalizedCoordinate_eq_restricted
#print axioms SurveyStatements.P5OperatorReduction.norm_innerMatrixHaarReader_eq_one
#print axioms SurveyStatements.P5OperatorReduction.innerMatrixNormalizedCoordinate_sum_le
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionInnerMatrix_column_sum_le
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionInnerMatrix_variance_le_inverse_card
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionInnerMatrixVariance_eq_raw
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionInnerMatrix_variance_uniform_small_norm_bound
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionInnerMatrix_refinement_family_sum_eventually_small
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionInnerMatrix_exists_refinement_family_sum_small

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in operator-reduction inner matrix: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; operator-reduction inner L1 matrix has no unfinished proofs."
