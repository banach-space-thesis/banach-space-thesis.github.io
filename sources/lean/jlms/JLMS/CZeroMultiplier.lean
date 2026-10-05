import JLMS.CZeroTools

/-!
# Bounded diagonal operators on c₀

Pointwise multiplication by any bounded scalar sequence preserves c₀ and
has norm bounded by the scalar supremum. Positive real diagonals bounded
below by γ have reciprocal multipliers with norm at most 1/γ and exact
inverse identities. These provide the diagonal normalization of the matrix
factorization argument.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable (d : ℕ → 𝕜) (C : ℝ) (hC : 0 ≤ C) (hd : ∀ n, ‖d n‖ ≤ C)

def cZeroMultiplierValues (a : cZero 𝕜) : cZero 𝕜 where
  toFun n := d n * a n
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => C * ‖a n‖) (cocompact ℕ) (𝓝 0) from
        by simpa using (tendsto_const_nhds (x := C)).mul a.zero_at_infty'.norm)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hd n) (norm_nonneg _)

include hC in
theorem norm_cZeroMultiplierValues_le (a : cZero 𝕜) :
    ‖cZeroMultiplierValues d C hd a‖ ≤ C * ‖a‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg a))).mpr
  intro n
  change ‖d n * a n‖ ≤ C * ‖a‖
  rw [norm_mul]
  exact mul_le_mul (hd n) (norm_CZero_apply_le a n) (norm_nonneg _) hC

def cZeroMultiplier : cZero 𝕜 →L[𝕜] cZero 𝕜 :=
  ({ toFun := cZeroMultiplierValues d C hd
     map_add' a b := by ext n; exact mul_add _ _ _
     map_smul' c a := by ext n; change d n * (c * a n) = c * (d n * a n); ring } :
      cZero 𝕜 →ₗ[𝕜] cZero 𝕜).mkContinuous C (norm_cZeroMultiplierValues_le d C hC hd)

theorem norm_cZeroMultiplier_le : ‖cZeroMultiplier d C hC hd‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact norm_cZeroMultiplierValues_le d C hC hd

@[simp] theorem cZeroMultiplier_apply (a : cZero 𝕜) (n : ℕ) :
    cZeroMultiplier d C hC hd a n = d n * a n := rfl

/-- The inverse multiplier for a positive real diagonal bounded below by γ. -/
def cZeroReciprocalMultiplier (r : ℕ → ℝ) {γ : ℝ} (hγ : 0 < γ) (hr : ∀ n, γ ≤ r n) :
    cZero 𝕜 →L[𝕜] cZero 𝕜 :=
  cZeroMultiplier (fun n => ((r n)⁻¹ : 𝕜)) (1 / γ) (one_div_pos.mpr hγ).le (fun n => by
    change ‖(r n : 𝕜)⁻¹‖ ≤ 1 / γ
    rw [norm_inv, RCLike.norm_ofReal, abs_of_pos (hγ.trans_le (hr n))]
    simpa only [one_div] using one_div_le_one_div_of_le hγ (hr n))

theorem norm_cZeroReciprocalMultiplier_le (r : ℕ → ℝ) {γ : ℝ}
    (hγ : 0 < γ) (hr : ∀ n, γ ≤ r n) :
    ‖cZeroReciprocalMultiplier (𝕜 := 𝕜) r hγ hr‖ ≤ 1 / γ := norm_cZeroMultiplier_le _ _ _ _

end JLMS
