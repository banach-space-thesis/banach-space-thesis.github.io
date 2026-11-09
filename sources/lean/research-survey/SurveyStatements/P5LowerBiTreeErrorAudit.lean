import SurveyStatements.P5LowerBiTreeErrorSeries
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
      throwError "Unapproved axiom in lower bi-tree errors: {axiomName}"
  logInfo m!"Audited {declarations.length} lower-error declarations without admissions."

#print axioms SurveyStatements.P5.exists_diagonalGrid_norm_limit
#print axioms SurveyStatements.P5.exists_superdiagonalGrid_norm_limit
#print axioms SurveyStatements.P5.norm_lowerBiTreeError_le
#print axioms SurveyStatements.P5.lowerBiTreeError_productHaar
