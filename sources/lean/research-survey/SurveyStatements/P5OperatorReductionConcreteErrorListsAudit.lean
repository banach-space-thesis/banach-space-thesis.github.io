import SurveyStatements.P5OperatorReductionConcreteOuterErrorLists
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
      throwError "Unapproved concrete finite error-list axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} concrete finite error-list declarations without admissions."

#print axioms SurveyStatements.P5OperatorReduction.exists_concrete_inner_step_of_actual_moments
#print axioms SurveyStatements.P5OperatorReduction.exists_concrete_outer_step_of_actual_moments
