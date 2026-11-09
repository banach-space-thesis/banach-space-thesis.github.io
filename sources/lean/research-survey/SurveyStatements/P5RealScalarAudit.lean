import SurveyStatements.P5RealScalarRestricted
import SurveyStatements.P5RealScalarOperator
import SurveyStatements.P5RealScalarCapon
import Lean

/-! A strict transitive audit, with no admission exceptions. -/
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
      throwError "Unapproved axiom in real-scalar dependency graph: {axiomName}"
  logInfo m!"Audited {declarations.length} real-scalar declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P5.RealScalar.retraction_embedding
#print axioms SurveyStatements.P5.RealScalar.norm_embedding_apply
#print axioms SurveyStatements.P5.RealScalar.embedding_outerExpectation
#print axioms SurveyStatements.P5.RealScalar.embedding_innerExpectation
#print axioms SurveyStatements.P5.RealScalar.retraction_mem_doublyZeroMean
#print axioms SurveyStatements.P5.RealScalar.embedding_productHaar
#print axioms SurveyStatements.P5.RealScalar.cancellative_retraction
#print axioms SurveyStatements.P5.RealScalar.operator_productHaar_cut
#print axioms SurveyStatements.P5.no_capon_operator
#print axioms SurveyStatements.P5.no_cancellative_capon_operator
