import SurveyStatements.P5HaarSubsequenceTrace
import SurveyStatements.P5VectorPartitionIndicators
import SurveyStatements.P5VectorPartitionNatural
import SurveyStatements.P5StableGeneratorLimit
import Lean

/-! Transitive axiom audit of concrete P5 constructions, without importing
the unfinished main theorem. No declaration receives an admission exception. -/

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
      throwError "Unapproved axiom in P5 construction dependency graph: {axiomName}"
  logInfo m!"Audited {declarations.length} construction declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5.innerHaar_diagonal_subsequence_trace
#print axioms SurveyStatements.P5.norm_vectorLpPartitionTransfer_le
#print axioms SurveyStatements.P5.vectorLpPartitionTransfer_indicator
#print axioms SurveyStatements.P5.vectorLpPartitionTransfer_natural
#print axioms SurveyStatements.P5.exists_operator_of_stable_generators
