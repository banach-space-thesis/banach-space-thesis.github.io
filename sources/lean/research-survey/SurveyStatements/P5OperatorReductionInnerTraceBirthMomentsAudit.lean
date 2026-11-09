import SurveyStatements.P5OperatorReductionInnerTraceBirthMoments
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5OperatorReduction.packetReader_second_moment_eq_weighted_variance
#print axioms SurveyStatements.P5OperatorReduction.actualNormalizedInnerTrace_birth_target_moment_tendsto_zero
#print axioms SurveyStatements.P5OperatorReduction.actualNormalizedInnerTrace_birth_source_moment_tendsto_zero

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in actual inner-trace birth moments: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; actual inner-trace birth moments have no unfinished proofs."
