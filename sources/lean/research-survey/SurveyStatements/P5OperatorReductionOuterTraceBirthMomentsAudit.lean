import SurveyStatements.P5OperatorReductionOuterTraceBirthMoments
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
      throwError "Unapproved axiom in actual outer-trace birth moment graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported actual outer-trace birth moment declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5OperatorReduction.actualNormalizedOuterTrace_birth_target_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.actualNormalizedOuterTrace_birth_source_moment_tendsto_zero
