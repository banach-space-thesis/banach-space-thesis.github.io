import SurveyStatements.P5OperatorReductionSignedLpGrowthScaling
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
      throwError "Unapproved axiom in signed Lp growth graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported fourth moment and signed Lp growth declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.finite_sign_fourth_moment_le
#print axioms SurveyStatements.P5OperatorReduction.finite_sign_normalized_rpow_moment_le
#print axioms SurveyStatements.P5OperatorReduction.finite_Lp_norm_moment
#print axioms SurveyStatements.P5OperatorReduction.mean_signedLp_norm_rpow_le
#print axioms SurveyStatements.P5OperatorReduction.uniform_signedLp_tiny_family_mean_small
#print axioms SurveyStatements.P5OperatorReduction.uniform_signedLp_mean_ratio_small
#print axioms SurveyStatements.P5OperatorReduction.tendsto_signedLp_mean_ratio_zero
