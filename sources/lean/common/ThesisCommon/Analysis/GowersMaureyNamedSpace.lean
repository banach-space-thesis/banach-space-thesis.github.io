import ThesisCommon.Analysis.GowersMaureySpace
import ThesisCommon.Analysis.GowersMaureyConstructionExists

/-! A named actual shift-generated Gowers--Maurey Banach space, after
proving existence of its rapid-growth and rational coding data.
No operator-theoretic property is used in choosing those data.
-/
noncomputable section
namespace ThesisCommon

/-- The actual completion from Gowers--Maurey §4.2, with fixed admissible
construction choices. This is distinct from their scalar-plus-strictly-
singular HI space. The assertion that it is prime is a separate goal. -/
abbrev ShiftGowersMaureySpace (𝕜 : Type*) [RCLike 𝕜] :=
  GowersMaurey.ShiftSpace (GowersMaurey.chosenConstructionData 𝕜)

end ThesisCommon
