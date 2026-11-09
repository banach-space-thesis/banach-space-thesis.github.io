import SurveyStatements.P5OperatorReductionConcreteEntryBirthMoments
import SurveyStatements.P5OperatorReductionConcreteBalanceMoments
import SurveyStatements.P5OperatorReductionBornPairMoments
import SurveyStatements.P5OperatorReductionOuterTraceBirthMoments
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
      throwError "Unapproved concrete selection moment axiom: {axiomName}"
  logInfo m!"STRICT concrete selection moments: {declarations.length} declarations, standard three axioms only"

#print axioms SurveyStatements.P5OperatorReduction.concrete_entry_inner_source_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.concrete_entry_inner_target_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.concrete_entry_outer_source_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.concrete_entry_outer_target_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.actualNormalizedOuterTrace_balance_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.actualNormalizedInnerTrace_balance_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.born_pair_moment_tendsto_zero
