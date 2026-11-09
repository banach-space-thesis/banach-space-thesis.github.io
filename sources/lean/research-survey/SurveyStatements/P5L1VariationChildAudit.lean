import SurveyStatements.P5L1VariationFiniteAudit
import SurveyStatements.P5L1VariationLocalDiagonal
import SurveyStatements.P5L1VariationLocalLimits
import SurveyStatements.P5L1VariationLocalCellTrace
import SurveyStatements.P5L1VariationBoundedSteps
import SurveyStatements.P5L1VariationArbitraryDensity
import SurveyStatements.P5L1VariationOriginalLocalTrace
import Lean

open Lean Elab Command
run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements.P5L1Variation).isPrefixOf name ||
    (`SurveyStatements.P5Support).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved local dyadic diagonalization axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} local dyadic diagonalization/support declarations without admissions."

#print axioms SurveyStatements.P5L1Variation.childFlip_haar_neg
#print axioms SurveyStatements.P5L1Variation.childFlip_other_haar
#print axioms SurveyStatements.P5L1Variation.terminalPermutation_coordinate_of_fixed_haar
#print axioms SurveyStatements.P5L1Variation.localFiniteReynolds_coordinate_zero
#print axioms SurveyStatements.P5L1Variation.localFiniteReynolds_haar_average
#print axioms SurveyStatements.P5L1Variation.arbitrary_operator_local_average_limit
#print axioms SurveyStatements.P5L1Variation.exists_Linfty_of_full_cell_traces
#print axioms SurveyStatements.P5L1Variation.equalDyadicLevelAverage_eq_descendant_average
#print axioms SurveyStatements.P5L1Variation.original_local_L1_trace
