import SurveyStatements.P5OperatorReductionOuterShadowTraceValues
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
      throwError "Unapproved axiom in actual unnormalized inner trace graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported actual unnormalized inner trace declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.norm_innerSliceDyadicTraceValue_le
#print axioms SurveyStatements.P5OperatorReduction.innerSliceDyadicTraceValue_full_tendsto
#print axioms SurveyStatements.P5OperatorReduction.innerSliceDyadicTraceValue_equal_sets
#print axioms SurveyStatements.P5OperatorReduction.innerSliceDyadicTraceValue_additive
#print axioms SurveyStatements.P5OperatorReduction.innerSliceDyadicTraceValue_reservoir_tendsto
