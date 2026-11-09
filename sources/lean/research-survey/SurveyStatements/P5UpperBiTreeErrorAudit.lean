import SurveyStatements.P5UpperBiTreeErrorGeometricBudget
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5.upperDiagonalErrorTerm_productHaar
#print axioms SurveyStatements.P5.upperCoordinateErrorTerm_productHaar
#print axioms SurveyStatements.P5.upperBiTreeError_productHaar
#print axioms SurveyStatements.P5.norm_upperBiTreeError_le
#print axioms SurveyStatements.P5.norm_upperBiTreeError_geometric_le

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in upper bi-tree error series: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; upper bi-tree error series has no unfinished proofs."
