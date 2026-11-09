import SurveyStatements.P5CaponRealAudit
import SurveyStatements.P5CaponScalarRigidityRCLike
import SurveyStatements.P5DyadicGridLinear
import SurveyStatements.P5OperatorSeriesBounds
import SurveyStatements.P5GridStabilityNormLimits
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
      throwError "Unapproved axiom in grid operators: {axiomName}"
  logInfo m!"Audited {declarations.length} grid-operator declarations without admissions."

#print axioms SurveyStatements.P5.cancellative_triangular_operator_eq_scalar
#print axioms SurveyStatements.P5.norm_mixedDyadicGridOperator_sub_le
#print axioms SurveyStatements.P5.norm_operator_tsum_le
#print axioms SurveyStatements.P5.exists_diagonalGrid_norm_limit
#print axioms SurveyStatements.P5.exists_superdiagonalGrid_norm_limit
