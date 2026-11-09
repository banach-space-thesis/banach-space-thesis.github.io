import SurveyStatements.P5Support.LpHaarMultiplierStabilization
import Lean

/-! Transitive audit of the scalar stabilization support. There are no admitted exceptions. -/

open Lean Elab Command

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements.P5Support).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved transitive scalar-support axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} imported scalar-support declarations without admissions."

#print axioms SurveyStatements.P5Support.lpHaar_multiplier_scalar_compression
#print axioms SurveyStatements.P5Support.lpHaar_diagonal_edge_meanZero_bound
#print axioms SurveyStatements.P5Support.lpHaar_geometric_edge_budget
#print axioms SurveyStatements.P5Support.lpHaar_infinite_trace_selection
#print axioms SurveyStatements.P5Support.LpHaarSequentialSplits.compression_multiplier
