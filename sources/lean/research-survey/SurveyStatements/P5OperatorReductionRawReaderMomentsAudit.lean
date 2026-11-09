import SurveyStatements.P5OperatorReductionRawReaderMoments
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
      throwError "Unapproved axiom in actual raw and normalized reader moments: {axiomName}"
  logInfo m!"Audited {declarations.length} imported actual raw and normalized reader moment declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.rawScalarPacketReader_eq_signedHaarPacketReader
#print axioms SurveyStatements.P5OperatorReduction.uniform_rawScalarPacketReader_second_moment_small
#print axioms SurveyStatements.P5OperatorReduction.limiting_rawScalarPacketReader_second_moment_small
#print axioms SurveyStatements.P5OperatorReduction.mean_signedBlockReader_sq_eq_mass_scaled
#print axioms SurveyStatements.P5OperatorReduction.uniform_signedBlockReader_second_moment_small
#print axioms SurveyStatements.P5OperatorReduction.limiting_signedBlockReader_second_moment_small
