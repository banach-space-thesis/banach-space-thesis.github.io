import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.CZeroOperators

/-! Actual arbitrary-set coordinate suppressions on the standard sequence spaces. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def lpCoordinateProjection (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set Γ) :
    lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p :=
  lpDiagonal p (fun γ => if γ ∈ A then ContinuousLinearMap.id 𝕜 X else 0)
    1 zero_le_one (fun γ => by dsimp only; split_ifs; exact ContinuousLinearMap.norm_id_le; simp)

@[simp] theorem lpCoordinateProjection_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : Set Γ) (x : lp (fun _ : Γ => X) p) (γ : Γ) :
    lpCoordinateProjection (𝕜 := 𝕜) p A x γ = if γ ∈ A then x γ else 0 := by
  by_cases h : γ ∈ A <;> simp [lpCoordinateProjection, h]

theorem norm_lpCoordinateProjection_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set Γ) :
    ‖lpCoordinateProjection (𝕜 := 𝕜) (X := X) p A‖ ≤ 1 := norm_lpDiagonal_le _ _ _ _

theorem lpCoordinateProjection_idempotent (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set Γ) :
    (lpCoordinateProjection (𝕜 := 𝕜) (X := X) p A).comp
      (lpCoordinateProjection p A) = lpCoordinateProjection p A := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext γ
  change lpCoordinateProjection p A (lpCoordinateProjection p A x) γ = _
  by_cases h : γ ∈ A <;> simp [h]

section CZero
variable [TopologicalSpace Γ] [DiscreteTopology Γ]

def cZeroCoordinateProjection (A : Set Γ) : C₀(Γ, X) →L[𝕜] C₀(Γ, X) :=
  cZeroDiagonal (fun γ => if γ ∈ A then ContinuousLinearMap.id 𝕜 X else 0)
    1 zero_le_one (fun γ => by dsimp only; split_ifs; exact ContinuousLinearMap.norm_id_le; simp)

@[simp] theorem cZeroCoordinateProjection_apply (A : Set Γ) (x : C₀(Γ, X)) (γ : Γ) :
    cZeroCoordinateProjection (𝕜 := 𝕜) A x γ = if γ ∈ A then x γ else 0 := by
  by_cases h : γ ∈ A <;> simp [cZeroCoordinateProjection, h]

theorem norm_cZeroCoordinateProjection_le (A : Set Γ) :
    ‖cZeroCoordinateProjection (𝕜 := 𝕜) (X := X) A‖ ≤ 1 := norm_cZeroDiagonal_le _ _ _ _

theorem cZeroCoordinateProjection_idempotent (A : Set Γ) :
    (cZeroCoordinateProjection (𝕜 := 𝕜) (X := X) A).comp
      (cZeroCoordinateProjection A) = cZeroCoordinateProjection A := by
  apply ContinuousLinearMap.ext
  intro x
  ext γ
  change cZeroCoordinateProjection A (cZeroCoordinateProjection A x) γ = _
  by_cases h : γ ∈ A <;> simp [h]

end CZero
end ThesisCommon
