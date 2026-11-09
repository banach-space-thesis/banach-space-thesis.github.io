import SurveyStatements.P5GridStabilityNormLimits

/-! Uniform norm estimates for actual one-coordinate grid increments. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace SurveyStatements.P5
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def symbolGrid (d : DyadicIndex → DyadicIndex → 𝕜) (n m : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  mixedDyadicGridOperator n m (fun i j => d ⟨n, i⟩ ⟨m, j⟩)

theorem norm_symbolGrid_outer_step_le (d : DyadicIndex → DyadicIndex → 𝕜)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ)
    (n j : ℕ) (hjn : j ≤ n) (hη : 0 ≤ η n j) :
    ‖symbolGrid (p := p) d (n + 1) j - symbolGrid d n j‖ ≤ η n j := by
  have href : mixedDyadicGridOperator (p := p) (n + 1) j
      (fun i k => d ⟨n, lpHaarParentIndex n i⟩ ⟨j, k⟩) = symbolGrid d n j := by
    exact mixedDyadicGridOperator_refine_outer (𝕜 := 𝕜) (p := p) n j
      (fun i k => d ⟨n, i⟩ ⟨j, k⟩)
  rw [← href]
  unfold symbolGrid
  apply norm_mixedDyadicGridOperator_sub_le (p := p) _ _ _ _ hη
  intro i k
  obtain ⟨b, hb⟩ := dyadicIndex_eq_child_parent n i
  have h := hs.lower ⟨n, lpHaarParentIndex n i⟩ ⟨j, k⟩ b hjn
  simpa only [hb] using h.le

theorem norm_symbolGrid_inner_step_le (d : DyadicIndex → DyadicIndex → 𝕜)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ)
    (i n : ℕ) (hin : i < n) (hη : 0 ≤ η i n) :
    ‖symbolGrid (p := p) d i (n + 1) - symbolGrid d i n‖ ≤ η i n := by
  have href : mixedDyadicGridOperator (p := p) i (n + 1)
      (fun k j => d ⟨i, k⟩ ⟨n, lpHaarParentIndex n j⟩) = symbolGrid d i n := by
    exact mixedDyadicGridOperator_refine_inner (𝕜 := 𝕜) (p := p) i n
      (fun k j => d ⟨i, k⟩ ⟨n, j⟩)
  rw [← href]
  unfold symbolGrid
  apply norm_mixedDyadicGridOperator_sub_le (p := p) _ _ _ _ hη
  intro k j
  obtain ⟨b, hb⟩ := dyadicIndex_eq_child_parent n j
  have h := hs.upper ⟨i, k⟩ ⟨n, lpHaarParentIndex n j⟩ b hin
  simpa only [hb] using h.le

end SurveyStatements.P5
