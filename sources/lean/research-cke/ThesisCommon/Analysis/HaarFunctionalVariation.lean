import ThesisCommon.Analysis.HaarSignSecondMoment
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Total variation and variance estimates for bounded functionals on
disjoint Haar atoms. Norming phases make the proof valid over complex
scalars without an identification of the Lp dual. -/

noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def haarNormingPhase (z : 𝕜) : 𝕜 := if z = 0 then 0 else (‖z‖ : 𝕜) / z

theorem haarNormingPhase_norm_le (z : 𝕜) : ‖haarNormingPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [haarNormingPhase, hz]
  · simp [haarNormingPhase, hz, norm_div, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg z), norm_ne_zero_iff.mpr hz]

theorem haarNormingPhase_mul (z : 𝕜) : haarNormingPhase z * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [haarNormingPhase, hz]
  · simp [haarNormingPhase, hz]

theorem haar_functional_variation_le {n : ℕ} (v : Fin n → X) (φ : X →L[𝕜] 𝕜)
    {C : ℝ} (hv : ∀ a : Fin n → 𝕜, (∀ i, ‖a i‖ ≤ 1) → ‖∑ i, a i • v i‖ ≤ C) :
    (∑ i, ‖φ (v i)‖) ≤ ‖φ‖ * C := by
  let a : Fin n → 𝕜 := fun i => haarNormingPhase (φ (v i))
  have heq : φ (∑ i, a i • v i) = ((∑ i, ‖φ (v i)‖ : ℝ) : 𝕜) := by
    simp only [map_sum, map_smul, smul_eq_mul, a, haarNormingPhase_mul, RCLike.ofReal_sum]
  have hnorm : ‖φ (∑ i, a i • v i)‖ = ∑ i, ‖φ (v i)‖ := by
    rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
  calc
    _ = ‖φ (∑ i, a i • v i)‖ := hnorm.symm
    _ ≤ ‖φ‖ * ‖∑ i, a i • v i‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * C := mul_le_mul_of_nonneg_left
      (hv a (fun i => haarNormingPhase_norm_le _)) (norm_nonneg φ)

theorem haar_functional_variance_le {n : ℕ} (v : Fin n → X) (φ : X →L[𝕜] 𝕜)
    {r C : ℝ} (hr : 0 ≤ r) (hn : ∀ i, ‖v i‖ ≤ r)
    (hv : ∀ a : Fin n → 𝕜, (∀ i, ‖a i‖ ≤ 1) → ‖∑ i, a i • v i‖ ≤ C) :
    (∑ i, ‖φ (v i)‖ ^ 2) ≤ (‖φ‖ * r) * (‖φ‖ * C) := by
  apply haar_sign_variance_le (fun i => φ (v i)) (mul_nonneg (norm_nonneg _) hr)
  · intro i
    exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hn i) (norm_nonneg φ))
  · exact haar_functional_variation_le v φ hv

end ThesisCommon
