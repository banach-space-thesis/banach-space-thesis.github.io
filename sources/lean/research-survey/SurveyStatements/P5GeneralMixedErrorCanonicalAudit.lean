import SurveyStatements.P5GeneralMixedErrorCanonicalReduction
import SurveyStatements.P5GeneralMixedErrorTraceStripsAudit
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
      throwError "Unapproved axiom in canonical mixed reduction: {axiomName}"
  logInfo m!"Audited {declarations.length} canonical mixed reduction declarations without admissions."

#print axioms SurveyStatements.P5.mixedNuclearError_canonical_coordinate
#print axioms SurveyStatements.P5.faithful_arbitrary_multiplier_reduction_of_matrix
