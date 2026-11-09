import SurveyStatements.P5OperatorReductionMatrixAbsoluteRefinement
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5OperatorReduction.packetMatrix_refineAt_card
#print axioms SurveyStatements.P5OperatorReduction.packetMatrix_refineAt_reservoir_card_tendsto_atTop
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_refineAt_family_sum_uniform_small
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionInnerMatrix_refineAt_family_sum_uniform_small
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionPacketMatrix_refineAt_family_sum_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionInnerMatrix_refineAt_family_sum_tendsto_zero

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in absolute matrix refinement: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; absolute matrix refinements have no unfinished proofs."
