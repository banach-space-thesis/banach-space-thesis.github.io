import ThesisCommon.Analysis.GowersMaureyOperatorTargets

/-! Exact conclusion targets for Example 7.1 on the actual shift-generated
Gowers--Maurey completion. Complex scalars are explicit, as required for
the printed unit-circle maximal-ideal description. Free construction data
remain parameters; their existence is proved in GowersMaureyNamedStatements.
All original conclusions are proved in PFP.GowersMaureyProofs. The statements
remain separate from their construction and proof dependencies.
-/
noncomputable section
namespace PFP
open ThesisCommon

/-- Nonvacuity of the source's rapid-growth and rational coding choices.
This must be proved before selecting an unparameterized named space. -/
def GowersMaureyConstructionExists : Prop := Nonempty (GowersMaurey.ConstructionData ℂ)

/-- Example 7.1, `Primariness does not imply PFP`, for every admissible choice
in the genuine Section 4.2 shift-space construction. The usual HI
scalar-plus-strictly-singular Gowers--Maurey space is not used here. -/
def Example_7_1 (D : GowersMaurey.ConstructionData ℂ) : Prop :=
  let X := GowersMaurey.ShiftSpace D
  IsPrimeBanachSpace ℂ X ∧ IsPrimary ℂ X ∧
    HasStrictlySingularWienerQuotient ℂ X ∧
    AllMaximalIdealsContainStrictlySingular ℂ X ∧
    HasContinuumManyMaximalOperatorIdeals ℂ X ∧ ¬ HasPFP ℂ X

/-- Full nonvacuous construction-and-conclusion target, without an assumed
Banach space or an assumed operator-quotient property. -/
def Example_7_1_all_constructions : Prop :=
  GowersMaureyConstructionExists ∧ ∀ D, Example_7_1 D

end PFP
