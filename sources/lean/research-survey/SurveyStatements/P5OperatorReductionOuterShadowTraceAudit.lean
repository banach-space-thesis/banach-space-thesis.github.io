import SurveyStatements.P5OperatorReductionOuterShadowTrace
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
      throwError "Unapproved axiom in actual outer-shadow local-trace graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported actual outer-shadow local-trace declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.meanZeroInnerSlice_haarDiagonal
#print axioms SurveyStatements.P5OperatorReduction.outerHaarPacketShadow_descendants_weightedReader
#print axioms SurveyStatements.P5OperatorReduction.outerHaarPacketShadow_localTrace_tendsto
#print axioms SurveyStatements.P5OperatorReduction.outerHaarPacketShadow_localTrace_reservoir_tendsto
#print axioms SurveyStatements.P5OperatorReduction.norm_innerSliceLocalTrace_le
