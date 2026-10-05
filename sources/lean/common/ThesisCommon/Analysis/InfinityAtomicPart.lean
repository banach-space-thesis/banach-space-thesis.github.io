import ThesisCommon.Analysis.InfinityScalarRows

/-! The bounded matrix part of an ell_infinity functional, defined by an
absolutely convergent scalar series. Its residual vanishes on unit vectors;
it need not vanish on all of ell_infinity.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem infinity_weighted_coefficients_summable
    (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) (x : lp (fun _ : ℕ => 𝕜) ∞) :
    Summable (fun n => x n * φ (lp.single ∞ n (1 : 𝕜))) := by
  apply ((infinity_functional_row_summable φ).mul_left ‖x‖).of_norm_bounded
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero x n) (norm_nonneg _)

theorem infinity_weighted_coefficients_norm_le
    (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) (x : lp (fun _ : ℕ => 𝕜) ∞) :
    ‖∑' n, x n * φ (lp.single ∞ n (1 : 𝕜))‖ ≤ ‖φ‖ * ‖x‖ := by
  calc
    _ ≤ ‖x‖ * ∑' n, ‖φ (lp.single ∞ n (1 : 𝕜))‖ := by
      apply tsum_of_norm_bounded ((infinity_functional_row_summable φ).hasSum.mul_left ‖x‖)
      intro n
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero x n) (norm_nonneg _)
    _ ≤ ‖x‖ * ‖φ‖ := mul_le_mul_of_nonneg_left (infinity_functional_row_tsum_le φ) (norm_nonneg _)
    _ = _ := mul_comm _ _

def infinityAtomicPart (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) :
    lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous {
    toFun := fun x => ∑' n, x n * φ (lp.single ∞ n (1 : 𝕜))
    map_add' := by
      intro x y
      simp only [lp.coeFn_add, Pi.add_apply, add_mul]
      exact (infinity_weighted_coefficients_summable φ x).tsum_add
        (infinity_weighted_coefficients_summable φ y)
    map_smul' := by
      intro a x
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact tsum_mul_left }
    ‖φ‖ (infinity_weighted_coefficients_norm_le φ)

theorem infinityAtomicPart_apply (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜)
    (x : lp (fun _ : ℕ => 𝕜) ∞) :
    infinityAtomicPart φ x = ∑' n, x n * φ (lp.single ∞ n (1 : 𝕜)) := rfl

theorem norm_infinityAtomicPart_le (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) :
    ‖infinityAtomicPart φ‖ ≤ ‖φ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

theorem infinityAtomicPart_single (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) (n : ℕ) :
    infinityAtomicPart φ (lp.single ∞ n (1 : 𝕜)) = φ (lp.single ∞ n (1 : 𝕜)) := by
  classical
  rw [infinityAtomicPart_apply, tsum_eq_single n]
  · rw [lp.single_apply_self, one_mul]
  · intro i hi
    rw [lp.single_apply_ne ∞ n 1 hi, zero_mul]

theorem infinity_residual_single (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) (n : ℕ) :
    (φ - infinityAtomicPart φ) (lp.single ∞ n (1 : 𝕜)) = 0 := by
  rw [ContinuousLinearMap.sub_apply, infinityAtomicPart_single, sub_self]

end ThesisCommon
