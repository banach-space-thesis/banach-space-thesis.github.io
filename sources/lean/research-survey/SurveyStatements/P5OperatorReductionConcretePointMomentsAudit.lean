import SurveyStatements.P5OperatorReductionConcretePointMoments
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
      throwError "Unapproved axiom in concrete point moments: {axiomName}"
  logInfo m!"Audited {declarations.length} imported concrete point-moment declarations; no unfinished proofs or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.concrete_outer_point_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.concrete_inner_point_moment_tendsto_zero
