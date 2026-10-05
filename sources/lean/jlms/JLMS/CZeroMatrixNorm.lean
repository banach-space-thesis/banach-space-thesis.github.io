import JLMS.CZeroSubsequencePairs

/-!
# Summable column bounds control the c₀ operator norm

The canonical coordinate expansion of a c₀ sequence converges in norm.
Apply the operator and a coordinate evaluation to that expansion. If the
absolute value of every matrix entry in column j is at most w_j, each
output coordinate is bounded by ‖a‖ times Σw_j. Taking the supremum gives
the operator norm bound. This controls the paired matrix error.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

theorem cZero_hasSum_units (a : cZero 𝕜) : HasSum (fun n => a n • cZeroUnit 𝕜 n) a := by
  have hd : Pairwise fun i j => Disjoint (Function.support (cZeroUnit 𝕜 i))
      (Function.support (cZeroUnit 𝕜 j)) := cZero_subsequenceUnits_disjoint id strictMono_id
  have hu : ∀ n, ‖cZeroUnit 𝕜 n‖ ≤ 1 := cZero_subsequenceUnits_norm_le id
  have hs := summable_smul_disjoint (cZeroUnit 𝕜) hu hd a
  have heq : (∑' n, a n • cZeroUnit 𝕜 n) = a := by
    ext i
    change evaluation i (∑' n, a n • cZeroUnit 𝕜 n) = a i
    rw [(evaluation i).map_tsum hs]
    simp only [map_smul, evaluation_apply, cZeroUnit_apply, smul_eq_mul]
    rw [tsum_eq_single i]
    · simp
    · intro n hn
      simp [Ne.symm hn]
  simpa only [heq] using hs.hasSum

theorem norm_cZero_operator_le_column_budget (B : cZero 𝕜 →L[𝕜] cZero 𝕜)
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    (hcoeff : ∀ i j, ‖B (cZeroUnit 𝕜 j) i‖ ≤ w j) : ‖B‖ ≤ ∑' j, w j := by
  apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg hw)
  intro a
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (tsum_nonneg hw) (norm_nonneg a))).mpr
  intro i
  have h := (cZero_hasSum_units a).map ((evaluation (𝕜 := 𝕜) i).comp B)
    ((evaluation (𝕜 := 𝕜) i).comp B).continuous
  have heq : B a i = ∑' j, a j * B (cZeroUnit 𝕜 j) i := by
    simpa only [Function.comp_def, map_smul, ContinuousLinearMap.comp_apply, evaluation_apply, smul_eq_mul] using
      h.tsum_eq.symm
  change ‖B a i‖ ≤ (∑' j, w j) * ‖a‖
  rw [heq]
  have hb (j : ℕ) : ‖a j * B (cZeroUnit 𝕜 j) i‖ ≤ ‖a‖ * w j := by
    rw [norm_mul]
    exact mul_le_mul (norm_CZero_apply_le a j) (hcoeff i j) (norm_nonneg _) (norm_nonneg _)
  have hn := (hsum.mul_left ‖a‖).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  calc
    _ ≤ ∑' j, ‖a j * B (cZeroUnit 𝕜 j) i‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j, ‖a‖ * w j := hn.tsum_le_tsum hb (hsum.mul_left ‖a‖)
    _ = (∑' j, w j) * ‖a‖ := by rw [tsum_mul_left, mul_comm]

end JLMS
