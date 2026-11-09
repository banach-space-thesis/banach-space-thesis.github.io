import SurveyStatements.P5OperatorReductionConcreteTraceBounds
import SurveyStatements.P5OperatorReductionNormBudgets
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
      throwError "Unapproved axiom in concrete operator-reduction bounds: {axiomName}"
  logInfo m!"Audited {declarations.length} imported concrete operator-reduction bound declarations; no unfinished proofs or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.exists_concrete_trees
#print axioms SurveyStatements.P5OperatorReduction.concrete_mixed_entry_bound
#print axioms SurveyStatements.P5OperatorReduction.exists_concrete_outer_stripe_multiplier
#print axioms SurveyStatements.P5OperatorReduction.exists_concrete_inner_stripe_multiplier
#print axioms SurveyStatements.P5OperatorReduction.exists_concrete_norm_budgets
