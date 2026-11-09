import SurveyStatements.P5OperatorReductionInnerShadowTrace
import Lean

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
      throwError "Unapproved axiom in genuine inner-shadow scalar trace graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported genuine inner-shadow scalar trace declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.rawHaarPacketShadowOperator_apply
#print axioms SurveyStatements.P5OperatorReduction.norm_rawHaarPacketShadowOperator_le
#print axioms SurveyStatements.P5OperatorReduction.rawHaarPacketShadow_scalar_eq_levelTrace
#print axioms SurveyStatements.P5OperatorReduction.normalizedRawShadow_blockReader_tendsto
