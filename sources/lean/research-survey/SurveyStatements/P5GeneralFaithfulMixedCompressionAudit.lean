import SurveyStatements.P5GeneralFaithfulMixedCompressionCancellative
import SurveyStatements.P5GeneralFaithfulMixedCompressionMatrix
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
      throwError "Unapproved axiom in general faithful mixed compression: {axiomName}"
  logInfo m!"Audited {declarations.length} general faithful-compression declarations without admissions."

#print axioms SurveyStatements.P5.faithfulMixed_rawA_coordinate
#print axioms SurveyStatements.P5.faithfulMixed_arbitrary_compression_coordinate
#print axioms SurveyStatements.P5.faithfulMixed_arbitrary_compression_coordinate_sum
#print axioms SurveyStatements.P5.faithfulMixedBlockReader_coordinate_sum
#print axioms SurveyStatements.P5.exists_faithful_arbitrary_compression_coordinates
#print axioms SurveyStatements.P5.faithfulMixed_arbitrary_compression_matrix_sum
