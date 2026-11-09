import SurveyStatements.P5OperatorReductionOuterShadowCoefficients
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
      throwError "Unapproved axiom in actual outer-shadow coefficient graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported actual outer-shadow coefficient declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.rawL1HaarPacket_reader_input_eq_diagonal_sum
#print axioms SurveyStatements.P5OperatorReduction.outerHaarPacketShadow_weightedReader
#print axioms SurveyStatements.P5OperatorReduction.outerHaarPacketShadow_haarReader
#print axioms SurveyStatements.P5OperatorReduction.outerHaarPacketShadow_weightedReader_coefficient
