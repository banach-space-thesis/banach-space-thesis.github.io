import SurveyStatements.P1SupportStabilization
import Lean

/-! Every imported survey declaration in the support-stabilization proof is
audited transitively, with no exception for unfinished helpers. -/

open Lean Elab Command

#print axioms SurveyStatements.P1.support_assignment_stabilization

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved transitive axiom in support stabilization: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; support stabilization has no unfinished proofs."
