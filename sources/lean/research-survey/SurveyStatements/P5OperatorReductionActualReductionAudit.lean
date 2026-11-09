import SurveyStatements.P5OperatorReductionActualReduction
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
      throwError "Unapproved axiom in actual arbitrary-operator reduction: {axiomName}"
  logInfo m!"Audited {declarations.length} imported actual arbitrary-operator reduction declarations; no unfinished proofs or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.arbitrary_operator_multiplier_compression
