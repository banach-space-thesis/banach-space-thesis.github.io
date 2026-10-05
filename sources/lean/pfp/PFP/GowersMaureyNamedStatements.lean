import PFP.GowersMaureyStatements
import ThesisCommon.Analysis.GowersMaureyNamedSpace

/-! The named Example 7.1 target, now based on a proved nonempty family of
actual implicit-norm completions. Construction existence is proved here;
primeness, the operator quotient, maximal ideals and failure of PFP are proved
separately in PFP.GowersMaureyProofs, without being assumed in the construction.
-/
noncomputable section
namespace PFP
open ThesisCommon

theorem gowersMaureyConstructionExists : GowersMaureyConstructionExists :=
  GowersMaurey.constructionData_nonempty

/-- Example 7.1 on the fixed actual complex shift-generated space. -/
def Example_7_1_named : Prop :=
  IsPrimeBanachSpace ℂ (ShiftGowersMaureySpace ℂ) ∧
    IsPrimary ℂ (ShiftGowersMaureySpace ℂ) ∧
    HasStrictlySingularWienerQuotient ℂ (ShiftGowersMaureySpace ℂ) ∧
    AllMaximalIdealsContainStrictlySingular ℂ (ShiftGowersMaureySpace ℂ) ∧
    HasContinuumManyMaximalOperatorIdeals ℂ (ShiftGowersMaureySpace ℂ) ∧
    ¬ HasPFP ℂ (ShiftGowersMaureySpace ℂ)

theorem example_7_1_named_iff :
    Example_7_1_named ↔ Example_7_1 (GowersMaurey.chosenConstructionData ℂ) := Iff.rfl

end PFP
