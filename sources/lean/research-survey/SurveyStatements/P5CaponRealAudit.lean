import SurveyStatements.P5CaponUnboundedReal
import SurveyStatements.P5CaponScalarRigidity
import SurveyStatements.P5MixedDyadicMeans
import SurveyStatements.P5PiecewiseOperatorLift
import Lean

/-! Strict transitive audit of the actual real Capon counterexample. -/
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
      throwError "Unapproved axiom in real Capon proof: {axiomName}"
  logInfo m!"Audited {declarations.length} real Capon declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5.leftLeafTest_eq_sum
#print axioms SurveyStatements.P5.l1SetReader_leftDyadicHaar
#print axioms SurveyStatements.P5.tendsto_caponInput
#print axioms SurveyStatements.P5.norm_caponRingReader_le
#print axioms SurveyStatements.P5.IsCaponOperator.ring_reader_input_lower
#print axioms SurveyStatements.P5.no_real_capon_operator
#print axioms SurveyStatements.P5.no_real_cancellative_capon_operator
#print axioms SurveyStatements.P5.real_cancellative_triangular_operator_eq_scalar
#print axioms SurveyStatements.P5.norm_mixedLowerStrip_le
#print axioms SurveyStatements.P5.norm_piecewiseOperatorLift_le
