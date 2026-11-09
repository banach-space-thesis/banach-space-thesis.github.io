import SurveyStatements.P5OperatorReductionOuterShadowTracePackets
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
      throwError "Unapproved axiom in arbitrary-packet physical-parent trace graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported arbitrary-packet physical-parent trace declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.outerHaarPacketShadow_weightedReader_parent_trace
#print axioms SurveyStatements.P5OperatorReduction.outerHaarPacketShadow_fixed_parent_tendsto
