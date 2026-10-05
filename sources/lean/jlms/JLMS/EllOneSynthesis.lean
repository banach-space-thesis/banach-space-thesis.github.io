import JLMS.L1Restriction

/-!
# The bounded synthesis operator from ℓ¹

Every uniformly bounded family of vectors in a Banach space determines a
bounded operator from ℓ¹ by its absolutely convergent scalar combination.
This reusable construction transfers a putative ℓ¹ embedding to the compact
image of its coordinate functions.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable (v : ℕ → E) (C : ℝ) (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C)

include hv in
theorem summable_ellOne_smul (a : ellOne 𝕜) : Summable (fun n => a n • v n) :=
  ((ellOneOn_summable_norm a).mul_right C).of_norm_bounded (fun n => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _))

include hC hv in
theorem norm_ellOne_synthesis_le (a : ellOne 𝕜) : ‖∑' n, a n • v n‖ ≤ C * ‖a‖ := by
  have hb (n : ℕ) : ‖a n • v n‖ ≤ ‖a n‖ * C := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _)
  have hn := ((ellOneOn_summable_norm a).mul_right C).of_nonneg_of_le
    (fun _ => norm_nonneg _) hb
  calc
    _ ≤ ∑' n, ‖a n • v n‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, ‖a n‖ * C := hn.tsum_le_tsum hb ((ellOneOn_summable_norm a).mul_right C)
    _ = C * ‖a‖ := by rw [tsum_mul_right, ellOneOn_norm_eq_tsum, mul_comm]

def ellOneSynthesis : ellOne 𝕜 →L[𝕜] E :=
  ({ toFun a := ∑' n, a n • v n
     map_add' a b := by
       change (∑' n, (a n + b n) • v n) = _
       simp_rw [add_smul]
       exact (summable_ellOne_smul v C hv a).tsum_add (summable_ellOne_smul v C hv b)
     map_smul' c a := by
       change (∑' n, (c * a n) • v n) = c • _
       simp_rw [mul_smul]
       exact (summable_ellOne_smul v C hv a).tsum_const_smul c } :
      ellOne 𝕜 →ₗ[𝕜] E).mkContinuous C (norm_ellOne_synthesis_le v C hC hv)

@[simp] theorem ellOneSynthesis_single (n : ℕ) :
    ellOneSynthesis v C hC hv (lp.single 1 n (1 : 𝕜)) = v n := by
  classical
  change (∑' j, (lp.single 1 n (1 : 𝕜) : ellOne 𝕜) j • v j) = v n
  rw [tsum_eq_single n]
  · simp
  · intro j hj
    simp [lp.single_apply, hj]

end JLMS
