import SurveyStatements.P5OperatorReductionEdgeMultipliers
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
      throwError "Unapproved axiom in actual edge multipliers: {axiomName}"
  logInfo m!"Audited {declarations.length} imported edge-multiplier declarations; no unfinished proofs or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.edgeTraceMultiplier_haar
#print axioms SurveyStatements.P5OperatorReduction.norm_edgeTraceMultiplier_le
#print axioms SurveyStatements.P5OperatorReduction.edgeTraceMultiplier_integral
