import SurveyStatements.P5OperatorReductionPacketDiagonalErrors
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5OperatorReduction.operatorReductionSignedBlockReader_eq_quadratic
#print axioms SurveyStatements.P5OperatorReduction.operatorReductionSignedBlock_diagonal_error_eq_centered

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in packet diagonal errors: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; actual packet diagonal errors have no unfinished proofs."
