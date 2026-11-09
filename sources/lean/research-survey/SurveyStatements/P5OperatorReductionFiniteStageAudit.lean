import SurveyStatements.P5OperatorReductionFiniteErrorsReservoir
import SurveyStatements.P5OperatorReductionOuterSlices
import SurveyStatements.P5OperatorReductionVarianceLimits
import SurveyStatements.P5OperatorReductionTraceMoments
import SurveyStatements.P5OperatorReductionInnerSlices
import Lean

open Lean Elab Command
run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements.P5OperatorReduction).isPrefixOf name ||
    (`SurveyStatements.P5L1Variation).isPrefixOf name ||
    (`SurveyStatements.P5Support).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved finite-stage trace/reservoir axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} finite-stage trace/reservoir/local-trace declarations without admissions."

#print axioms SurveyStatements.P5OperatorReduction.exists_registered_operator_traces
#print axioms SurveyStatements.P5OperatorReduction.exists_universal_inner_pair_traces
#print axioms SurveyStatements.P5OperatorReduction.exists_fixed_sign_errors_and_registered_traces
#print axioms SurveyStatements.P5OperatorReduction.signed_second_moment_bound_of_limit
#print axioms SurveyStatements.P5OperatorReduction.lpHaarTrace_split_second_moment_le
#print axioms SurveyStatements.P5OperatorReduction.norm_meanZeroInnerSlice_le
