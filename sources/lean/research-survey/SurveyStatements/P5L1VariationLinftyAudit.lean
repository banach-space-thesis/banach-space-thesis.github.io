import SurveyStatements.P5L1VariationLinfty
import Lean

open Lean Elab Command
run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements.P5L1Variation).isPrefixOf name ||
    (`SurveyStatements.P5Support).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved transitive L∞-trace axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} imported L∞-trace/support declarations without admissions."

#print axioms SurveyStatements.P5L1Variation.exists_full_trace_Linfty_density
