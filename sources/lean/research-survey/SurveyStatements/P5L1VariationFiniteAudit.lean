import SurveyStatements.P5L1VariationTreeFlips
import SurveyStatements.P5L1VariationTerminalGeometry
import SurveyStatements.P5L1VariationTerminalVectors
import SurveyStatements.P5L1VariationTreeHaar
import SurveyStatements.P5L1VariationLocalTree
import SurveyStatements.P5L1VariationTraceFromFinite
import SurveyStatements.P5L1VariationLpBoundClosed
import Lean

/-! Complete transitive finite-local branch and actual Reynolds construction
audit. No unfinished theorem or extra axiom is an allowed exception. -/
open Lean Elab Command
run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements.P5L1Variation).isPrefixOf name ||
    (`SurveyStatements.P5Support).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved finite-local/Reynolds axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} finite-local/Reynolds/support declarations without admissions."

#print axioms SurveyStatements.P5L1Variation.DyadicBranch.finite_variation_endpoints_le_local
#print axioms SurveyStatements.P5L1Variation.meanZero_finite_variation_endpoints_le_local
#print axioms SurveyStatements.P5L1Variation.terminalPermutation_norm_le
#print axioms SurveyStatements.P5L1Variation.terminalPermutation_mul
#print axioms SurveyStatements.P5L1Variation.terminalReynolds_norm_le
#print axioms SurveyStatements.P5L1Variation.terminalReynolds_commutes
#print axioms SurveyStatements.P5L1Variation.dyadicTree_transitive
#print axioms SurveyStatements.P5L1Variation.localXorTreePermutation_involutive
#print axioms SurveyStatements.P5L1Variation.terminalFiber_cells
#print axioms SurveyStatements.P5L1Variation.terminalPermutation_cell
#print axioms SurveyStatements.P5L1Variation.terminalPermutation_haar_signed
#print axioms SurveyStatements.P5L1Variation.localFiniteReynolds_norm_le
#print axioms SurveyStatements.P5L1Variation.localDyadicTree_transitive
#print axioms SurveyStatements.P5L1Variation.exists_limit_of_finite_branch_eigenoperators
#print axioms SurveyStatements.P5L1Variation.isClosed_ae_norm_bound

