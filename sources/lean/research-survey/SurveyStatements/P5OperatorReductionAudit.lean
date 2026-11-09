import SurveyStatements.P5L1VariationChildAudit
import SurveyStatements.P5L1VariationTraceFunctional
import SurveyStatements.P5OperatorReductionMoments
import SurveyStatements.P5OperatorReductionSignIdentity
import SurveyStatements.P5OperatorReductionFiniteDisjointification
import SurveyStatements.P5OperatorReductionDisjointMoments
import SurveyStatements.P5OperatorReductionReaderSigns
import SurveyStatements.P5OperatorReductionPairing
import SurveyStatements.P5OperatorReductionReaderAlgebra
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
      throwError "Unapproved arbitrary-operator reduction support axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} reduction/local-trace/support declarations without admissions."

#print axioms SurveyStatements.P5L1Variation.localTraceFunctional_tendsto
#print axioms SurveyStatements.P5OperatorReduction.centeredQuadraticForm_eq_diagonal_error
#print axioms SurveyStatements.P5OperatorReduction.centeredQuadraticForm_variance_le
#print axioms SurveyStatements.P5OperatorReduction.signed_reader_input_sum
#print axioms SurveyStatements.P5OperatorReduction.weightedOuterReader_tensor
#print axioms SurveyStatements.P5OperatorReduction.norm_jointWeightedReader_le
#print axioms SurveyStatements.P5OperatorReduction.exists_disjoint_norming_readers
#print axioms SurveyStatements.P5OperatorReduction.finite_disjointification_of_not_uniformSmallRestrictions
