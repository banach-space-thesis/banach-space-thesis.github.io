import SurveyStatements.P5CaponGridRigidity
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5.caponLocalized_embedded_input_image
#print axioms SurveyStatements.P5.mixedDyadicGridOperator_local_productHaar
#print axioms SurveyStatements.P5.mixedDyadicGridOperator_embedded_local_image
#print axioms SurveyStatements.P5.capon_square_grid_norm_closure_rigidity

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in localized grid rigidity: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; localized grid rigidity has no unfinished proofs."
