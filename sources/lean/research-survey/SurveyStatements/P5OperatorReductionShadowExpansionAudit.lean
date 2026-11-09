import SurveyStatements.P5OperatorReductionShadowExpansion
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
      throwError "Unapproved axiom in actual Haar shadow expansion graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported actual Haar shadow expansion declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.rawHaarPacket_signed_mask
#print axioms SurveyStatements.P5OperatorReduction.rawHaarPacket_input_signed_mask
#print axioms SurveyStatements.P5OperatorReduction.vectorMean_signed_reader_input_subset
#print axioms SurveyStatements.P5OperatorReduction.rawPacketReader_signed_mask
#print axioms SurveyStatements.P5OperatorReduction.rawHaarPacketShadow_eq_diagonal_sum
#print axioms SurveyStatements.P5OperatorReduction.normalized_rawHaarPacketShadow_eq_diagonal_sum
#print axioms SurveyStatements.P5OperatorReduction.rawL1PacketReader_signed_mask
#print axioms SurveyStatements.P5OperatorReduction.scalarHaarPacketReader_eq_radius_coefficient
#print axioms SurveyStatements.P5OperatorReduction.scalarHaarPacketReader_meanZeroProjection
#print axioms SurveyStatements.P5OperatorReduction.rawL1HaarPacket_reader_input_eq_diagonal_sum
