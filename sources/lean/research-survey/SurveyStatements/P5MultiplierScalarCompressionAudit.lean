import SurveyStatements.P5MultiplierScalarCompression
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
      throwError "Unapproved axiom in multiplier scalar compression: {axiomName}"
  logInfo m!"Audited {declarations.length} multiplier scalar-compression declarations without admissions."

#print axioms SurveyStatements.P5.stable_multiplier_grid_limits_eq
#print axioms SurveyStatements.P5.stable_multiplier_norm_sub_scalar_le
#print axioms SurveyStatements.P5.exists_fixed_scalar_multiplier_compression
#print axioms SurveyStatements.P5.productHaarMultiplier_scalar_compression
