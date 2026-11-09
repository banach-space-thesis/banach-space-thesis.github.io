import SurveyStatements.P5RademacherDecay
import SurveyStatements.P5RademacherReaders
import SurveyStatements.P5MixedSetReaders
import Lean

/-! Transitive audit of actual test vectors and readers. This file does not
assert the still outstanding Capon unboundedness theorem. -/

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
      throwError "Unapproved axiom in P5 test dependency graph: {axiomName}"
  logInfo m!"Audited {declarations.length} test declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5.norm_dyadicRademacherL2_sum_sq
#print axioms SurveyStatements.P5.norm_dyadicRademacherLp_le
#print axioms SurveyStatements.P5.norm_le_l2_moment_of_bound
#print axioms SurveyStatements.P5.norm_rademacherAverageLp_le
#print axioms SurveyStatements.P5.tendsto_rademacherAverageLp
#print axioms SurveyStatements.P5.rademacherReader_dyadicHaar
#print axioms SurveyStatements.P5.rademacherReader_level
#print axioms SurveyStatements.P5.sum_norm_l1SetReader_le
#print axioms SurveyStatements.P5.norm_mixedSetReader_le
#print axioms SurveyStatements.P5.mixedSetReader_tensor
