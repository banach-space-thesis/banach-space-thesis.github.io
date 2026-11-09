import SurveyStatements.P5L1VariationTrace
import Lean

/-! Transitive audit of the scalar multiplier full-sequence trace proof. -/
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
      throwError "Unapproved transitive scalar-trace axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} imported scalar-trace/support declarations without admissions."

#print axioms SurveyStatements.P5L1Variation.pointBranch
#print axioms SurveyStatements.P5L1Variation.stepSymbol_pointwise_exists_limit
#print axioms SurveyStatements.P5L1Variation.stepSymbol_setIntegral
#print axioms SurveyStatements.P5L1Variation.exists_full_trace_density
