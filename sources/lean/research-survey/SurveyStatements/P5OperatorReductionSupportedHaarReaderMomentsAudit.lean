import SurveyStatements.P5OperatorReductionSupportedHaarReaderMoments
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
      throwError "Unapproved axiom in actual supported Haar-reader moment graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported actual supported Haar-reader moment declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.norm_scalarHaarPacketReader_le
#print axioms SurveyStatements.P5OperatorReduction.scalarHaarPacketReader_eq_restricted
#print axioms SurveyStatements.P5OperatorReduction.uniform_signedHaarPacketReader_second_moment_small
#print axioms SurveyStatements.P5OperatorReduction.limiting_signedHaarPacketReader_second_moment_small
