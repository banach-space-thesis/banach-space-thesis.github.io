import SurveyStatements.P5OperatorReductionReservoirFusion
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
      throwError "Unapproved axiom in reservoir fusion: {axiomName}"
  logInfo m!"Audited {declarations.length} imported reservoir-fusion declarations; no unfinished proofs or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.reservoir_diagonal_strictMono
#print axioms SurveyStatements.P5OperatorReduction.reservoir_diagonal_preserves_registered_traces
