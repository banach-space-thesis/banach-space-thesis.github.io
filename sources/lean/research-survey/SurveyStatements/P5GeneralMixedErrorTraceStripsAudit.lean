import SurveyStatements.P5GeneralMixedErrorTraceStrips
import SurveyStatements.P5GeneralMixedErrorAudit
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
      throwError "Unapproved axiom in genuine trace strip construction: {axiomName}"
  logInfo m!"Audited {declarations.length} trace strip declarations without admissions."

#print axioms SurveyStatements.P5.exists_generalMixedOuterTraceStripSeries
#print axioms SurveyStatements.P5.exists_generalMixedInnerTraceStripSeries
