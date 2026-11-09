import SurveyStatements.P1ToroidalEltonOdell
import Lean

set_option maxHeartbeats 800000

/-! Strict audit of the original normed-space P1 statement and every
imported survey declaration. No admission or extra axiom is permitted. -/

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
      throwError "Unapproved axiom in complete P1 proof: {axiomName}"
  logInfo m!"Audited {declarations.length} declarations in the complete original P1 proof; no admissions or extra axioms."

#check SurveyStatements.P1.toroidal_elton_odell
#print axioms SurveyStatements.P1.toroidal_elton_odell
#print axioms SurveyStatements.P1.normalized_weakNull_toroidal_elton_odell
#print axioms SurveyStatements.P1.nontrivial_weakCauchy_toroidal_elton_odell
