import SurveyStatements.P4BlockBasis
import Lean

/-! Check every imported survey declaration and its transitive proof dependencies.
There are no admission exceptions in this component audit. -/

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
      throwError "Unapproved axiom in block-basis dependency graph: {axiomName}"
  logInfo m!"Audited {declarations.length} block-basis declarations; no admissions or extra axioms."

#print axioms SurveyStatements.P4.blockBasis_biorthogonal
#print axioms SurveyStatements.P4.blockBasis_span_dense
#print axioms SurveyStatements.P4.norm_blockBasis_orderedProjection_le
#print axioms SurveyStatements.P4.blockBasis_isSchauder
#print axioms SurveyStatements.P4.exists_reflexive_basis_retraction
