import SurveyStatements.P4BasisFactorization
import Lean

/-! Exhaustive transitive axiom audit of the original P4 theorem and every
survey declaration imported by its actual proof. No admission is permitted. -/

open Lean Elab Command

#print axioms SurveyStatements.P4.weaklyCompact_basis_factorization

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved transitive axiom in the P4 proof: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; P4 has no unfinished proofs."
