import ThesisCommon.Analysis.BanachMazurDistance

/-! Definition 2.1: actual multiplicative Banach–Mazur infimum and the
printed endpoint assertion. The latter is an unproved Prop specification;
source issue PFP-S03 records the missing infimum-attainment justification.
-/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type u) (Y : Type v)
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Definition 2.1's infimum, with infinity for an empty equivalence set
and the source's literal value zero for two zero Banach spaces. -/
abbrev Definition_2_1_distance : ℝ≥0∞ := banachMazurDistance 𝕜 X Y

/-- Definition 2.1's assertion as printed, retained without a proof.
PFP-S03: an infimum bound does not by itself supply an equivalence attaining
the endpoint C. No reverse implication is assumed or used elsewhere. -/
def Definition_2_1_asPrinted [CompleteSpace X] [CompleteSpace Y] (C : ℝ) : Prop :=
  1 ≤ C →
    (IsomorphicWithBound 𝕜 X Y C ↔ Definition_2_1_distance 𝕜 X Y ≤ ENNReal.ofReal C)

/-- The valid forward direction of the printed endpoint assertion. -/
theorem definition_2_1_forward {C : ℝ} (h : IsomorphicWithBound 𝕜 X Y C) :
    Definition_2_1_distance 𝕜 X Y ≤ ENNReal.ofReal C :=
  h.banachMazurDistance_le 𝕜 X Y

end PFP
