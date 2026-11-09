import SurveyStatements.P5L1VariationEndpoints
import Lean

/-! Complete transitive audit of scalar/cancellative L¹ branch necessity,
branch limits and full-sequence scalar traces, without admission exceptions. -/
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
      throwError "Unapproved transitive L1-variation/final axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} imported final L1-variation/support declarations without admissions."

#print axioms SurveyStatements.P5L1Variation.finite_branch_variation_endpoints_le
#print axioms SurveyStatements.P5L1Variation.meanZero_finite_branch_variation_endpoints_le
#print axioms SurveyStatements.P5L1Variation.extendMeanZero_norm_le
#print axioms SurveyStatements.P5L1Variation.meanZero_exists_full_trace_Linfty_density
