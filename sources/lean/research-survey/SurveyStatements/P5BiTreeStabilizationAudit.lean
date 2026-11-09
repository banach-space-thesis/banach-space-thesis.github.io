import SurveyStatements.P5BiTreeStabilizationDefinitions
import SurveyStatements.P5BiTreeStabilizationBalance
import SurveyStatements.P5BiTreeStabilizationTraces
import SurveyStatements.P5BiTreeStabilizationMeans
import SurveyStatements.P5BiTreeStabilizationHistory
import SurveyStatements.P5BiTreeStabilizationSelection
import SurveyStatements.P5BiTreeStabilizationBudget
import SurveyStatements.P5BiTreeStabilizationRectangleEstimates
import SurveyStatements.P5BiTreeStabilization
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
      throwError "Unapproved axiom in bi-tree stabilization graph: {axiomName}"
  logInfo m!"Audited {declarations.length} imported bi-tree declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5.BiTree.simultaneous_trace_balanced_split
#print axioms SurveyStatements.P5.BiTree.SignedTree.block_child_parent
#print axioms SurveyStatements.P5.BiTree.countable_trace_cluster
#print axioms SurveyStatements.P5.BiTree.simultaneous_trace_parent_select
#print axioms SurveyStatements.P5.BiTree.exists_iterated_trace_data
#print axioms SurveyStatements.P5.BiTree.blockAverage_norm_le
#print axioms SurveyStatements.P5.BiTree.exists_dependent_sequence_with_history
#print axioms SurveyStatements.P5.BiTree.exists_inner_step
#print axioms SurveyStatements.P5.BiTree.exists_outer_step
#print axioms SurveyStatements.P5.BiTree.exists_round_sequence
#print axioms SurveyStatements.P5.BiTree.roundOuterTree
#print axioms SurveyStatements.P5.BiTree.exists_round_error_budget
#print axioms SurveyStatements.P5.BiTree.exists_ordered_round_sequence
#print axioms SurveyStatements.P5.BiTree.roundOuterTree_strict_frequencies
#print axioms SurveyStatements.P5.BiTree.lower_slice_approx
#print axioms SurveyStatements.P5.BiTree.rectangle_inner_balance
#print axioms SurveyStatements.P5.BiTree.diagonal_edge_bound
#print axioms SurveyStatements.P5.BiTree.superdiagonal_edge_bound
#print axioms SurveyStatements.P5.BiTree.root_lower_bound
#print axioms SurveyStatements.P5.BiTree.root_upper_bound
#print axioms SurveyStatements.P5.BiTree.roundSymbol_semiStable
#print axioms SurveyStatements.P5.BiTree.exists_stabilized_trees
