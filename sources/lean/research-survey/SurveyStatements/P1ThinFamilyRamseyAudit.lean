import SurveyStatements.P1ThinFamilyRamsey
import Lean

/-! Exhaustive transitive audit of thin-family Ramsey and its foundations. -/
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
      throwError "Unapproved axiom in thin-family Ramsey: {axiomName}"
  logInfo m!"Audited {declarations.length} thin-family Ramsey declarations without admissions."

#print axioms SurveyStatements.P1.infinite_branch_extending_finset
#print axioms SurveyStatements.P1.thin_family_finiteColorRamsey
#print axioms SurveyStatements.P1.thin_family_homogeneous_at_minimum
#print axioms SurveyStatements.P1.thin_family_boundedColorRamsey
