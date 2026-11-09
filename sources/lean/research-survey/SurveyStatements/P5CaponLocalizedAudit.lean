import SurveyStatements.P5CaponLocalizedUnbounded
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5.tendsto_caponLocalizedInput
#print axioms SurveyStatements.P5.norm_caponLocalizedImage_lower
#print axioms SurveyStatements.P5.no_real_localized_capon_operator
#print axioms SurveyStatements.P5.no_real_localized_cancellative_capon_operator

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in localized Capon proof: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; localized Capon has no unfinished proofs."
