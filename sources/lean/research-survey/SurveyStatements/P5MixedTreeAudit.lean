import SurveyStatements.P5FaithfulMixedTrees
import SurveyStatements.P5VectorTensorLimits
import Lean

/-! Every imported survey declaration is checked transitively. There are
no unfinished main imports and no admission exceptions in this audit. -/

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
      throwError "Unapproved axiom in mixed-tree dependency graph: {axiomName}"
  logInfo m!"Audited {declarations.length} mixed-tree declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5.VectorPartitionTree.exists_faithful_retraction
#print axioms SurveyStatements.P5.VectorPartitionTree.forward_limit_tensor
#print axioms SurveyStatements.P5.VectorPartitionTree.backward_limit_integral
#print axioms SurveyStatements.P5.VectorPartitionTree.forward_limit_integral
#print axioms SurveyStatements.P5.innerLift_mem_doublyZeroMean
#print axioms SurveyStatements.P5.VectorPartitionTree.backward_limit_mem_doublyZeroMean
#print axioms SurveyStatements.P5.VectorPartitionTree.forward_limit_mem_doublyZeroMean
#print axioms SurveyStatements.P5.exists_restricted_contractive_retraction
#print axioms SurveyStatements.P5.exists_faithful_mixed_retraction
