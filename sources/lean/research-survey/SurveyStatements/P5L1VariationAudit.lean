import SurveyStatements.P5L1VariationLimit
import Lean

/-! Transitive audit of the actual scalar L¹ finite-branch necessity proof. -/
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
      throwError "Unapproved transitive L1-variation axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} imported L1-variation/support declarations without admissions."

#print axioms SurveyStatements.P5L1Variation.cellDensity_multiplier_difference
#print axioms SurveyStatements.P5L1Variation.DyadicBranch.sum_annulus_integral_norm_le
#print axioms SurveyStatements.P5L1Variation.prefixAverage_weighted_sum
#print axioms SurveyStatements.P5L1Variation.DyadicBranch.leafTest_image_on_annulus
#print axioms SurveyStatements.P5L1Variation.DyadicBranch.finite_defect_sum_le
#print axioms SurveyStatements.P5L1Variation.DyadicBranch.finite_variation_le
#print axioms SurveyStatements.P5L1Variation.multiplier_symbol_norm_le
#print axioms SurveyStatements.P5L1Variation.DyadicBranch.symbol_exists_limit
