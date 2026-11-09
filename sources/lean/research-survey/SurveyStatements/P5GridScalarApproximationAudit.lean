import SurveyStatements.P5GridScalarApproximation
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
      throwError "Unapproved axiom in grid scalar approximation graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported grid approximation declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5.scalarDyadicGridOperator_zero
#print axioms SurveyStatements.P5.mixedDyadicGridOperator_zero
#print axioms SurveyStatements.P5.diagonalGrid_zero
#print axioms SurveyStatements.P5.norm_diagonalGrid_limit_sub_scalar_le
#print axioms SurveyStatements.P5.diagonal_superdiagonal_difference_square
#print axioms SurveyStatements.P5.diagonal_superdiagonal_difference_square_approx
