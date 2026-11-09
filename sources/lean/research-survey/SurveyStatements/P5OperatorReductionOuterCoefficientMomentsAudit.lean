import SurveyStatements.P5OperatorReductionOuterCoefficientMoments
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5OperatorReduction.operatorReductionOuterWeightedCoefficient_eq_L1_coordinate
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionOuterWeightedCoefficient_sum_norm_le
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionOuterWeightedCoefficient_norm_le
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionOuterCoefficientVariance_eq_sum
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionOuterCoefficient_variance_le_norm_bound
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionOuterCoefficient_variance_bound_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionOuterCoefficient_family_sum_uniform_small

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in outer coefficient moments: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; outer coefficient moments have no unfinished proofs."
