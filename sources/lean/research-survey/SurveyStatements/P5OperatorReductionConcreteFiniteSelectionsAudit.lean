import SurveyStatements.P5OperatorReductionConcreteFiniteSelections

import Lean

open Lean Elab Command
run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements.P5OperatorReduction).isPrefixOf name ||
    (`SurveyStatements.P5Support).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved concrete finite selection axiom: {axiomName}"
  logInfo m!"STRICT concrete finite selections: {declarations.length} declarations, standard three axioms only"

#print axioms SurveyStatements.P5OperatorReduction.exists_actual_concrete_inner_step
#print axioms SurveyStatements.P5OperatorReduction.exists_actual_concrete_outer_step
