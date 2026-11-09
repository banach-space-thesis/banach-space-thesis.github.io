import SurveyStatements.P5OperatorReductionReservoir
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
      throwError "Unapproved axiom in reservoir selection: {axiomName}"
  logInfo m!"Audited {declarations.length} imported reservoir declarations; no unfinished proofs or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.exists_fixed_good_reservoir
#print axioms SurveyStatements.P5OperatorReduction.reservoir_preserves_registered_trace_limits
#print axioms SurveyStatements.P5OperatorReduction.reservoir_extract_countable_bounded_traces
