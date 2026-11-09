import SurveyStatements.P5GeneralMixedErrorReduction
import SurveyStatements.P5GeneralMixedErrorStripCoordinates
import SurveyStatements.P5GeneralMixedErrorIndexing
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
      throwError "Unapproved axiom in general mixed error operators: {axiomName}"
  logInfo m!"Audited {declarations.length} general mixed-error declarations without admissions."

#print axioms SurveyStatements.P5.norm_mixedNuclearError_le
#print axioms SurveyStatements.P5.mixedNuclearError_coordinate
#print axioms SurveyStatements.P5.exists_generalMixed_multiplier_of_error_coordinates
#print axioms SurveyStatements.P5.norm_generalMixedOuterStripSeries_le
#print axioms SurveyStatements.P5.norm_generalMixedInnerStripSeries_le
#print axioms SurveyStatements.P5.faithful_arbitrary_multiplier_reduction_of_errors
