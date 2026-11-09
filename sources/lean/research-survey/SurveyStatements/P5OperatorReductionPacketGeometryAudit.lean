import SurveyStatements.P5OperatorReductionPacketGeometryPointwise
import Lean

open Lean Elab Command

#print axioms SurveyStatements.P5.norm_operatorReductionRawHaarPacket_le
#print axioms SurveyStatements.P5.norm_operatorReductionNormalizedHaarPacket_le
#print axioms SurveyStatements.P5.norm_operatorReductionNormalizedHaarPacket_eq
#print axioms SurveyStatements.P5.operatorReductionUnitHaarPacket_refine_uniform_bound

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.constants.toList.filter (fun (name, _) =>
    (`SurveyStatements).isPrefixOf name)
  let (_, state) := ((declarations.forM (fun (name, _) =>
    CollectAxioms.collect name)).run env).run {}
  for axiomName in state.axioms do
    unless standard.contains axiomName do
      throwError "Unapproved axiom in operator-reduction packet geometry: {axiomName}"
  logInfo m!"Audited {declarations.length} imported survey declarations; operator-reduction packet geometry has no unfinished proofs."
