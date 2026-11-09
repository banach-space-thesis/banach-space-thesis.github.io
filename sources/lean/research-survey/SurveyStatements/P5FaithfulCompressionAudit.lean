import SurveyStatements.P5FaithfulMixedCompression
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
      throwError "Unapproved axiom in faithful mixed compression: {axiomName}"
  logInfo m!"Audited {declarations.length} faithful-compression declarations without admissions."

#print axioms SurveyStatements.P5.exists_faithfulTreeMaps
#print axioms SurveyStatements.P5Support.LpHaarSequentialSplits.reading_weighted_block
#print axioms SurveyStatements.P5.faithfulMixed_compression_productHaar
#print axioms SurveyStatements.P5.exists_faithful_multiplier_compression
