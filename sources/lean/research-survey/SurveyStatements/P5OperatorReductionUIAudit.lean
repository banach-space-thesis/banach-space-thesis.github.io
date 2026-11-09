import SurveyStatements.P5OperatorReductionAudit
import SurveyStatements.P5OperatorReductionRawShadows
import SurveyStatements.P5OperatorReductionPacketShadowBounds
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
      throwError "Unapproved actual-shadow uniform integrability axiom: {axiomName}"
  logInfo m!"Audited {declarations.length} actual-shadow/reduction/local-trace/support declarations without admissions."

#print axioms SurveyStatements.P5OperatorReduction.uniformSmallRestrictions_packetShadow
#print axioms SurveyStatements.P5OperatorReduction.uniformSmallRestrictions_rawHaarPacketShadow
#print axioms SurveyStatements.P5OperatorReduction.uniformIntegrable_packetShadow
#print axioms SurveyStatements.P5OperatorReduction.uniformSmallRestrictions_smul
#print axioms SurveyStatements.P5OperatorReduction.uniform_restricted_reader_signed_variance_small
