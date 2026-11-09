import SurveyStatements.P5OperatorReductionCountableBudgets
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
      throwError "Unapproved axiom in countable error budgets: {axiomName}"
  logInfo m!"Audited {declarations.length} countable-budget declarations; no unfinished proofs or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.exists_positive_countable_error_budget
