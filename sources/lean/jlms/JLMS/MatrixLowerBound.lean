import JLMS.CZeroSubsequencePairs
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# A nearly diagonal norming matrix bounds an operator below

Apply the ith norm-one functional to a c₀ combination of selected vectors.
Its diagonal contribution is at least γ times the ith coefficient, whereas
the summable off-diagonal column budget contributes at most ε times the
supremum norm. Taking the supremum over i gives the lower bound γ−ε.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem cZero_matrix_lower_bound (R : cZero 𝕜 →L[𝕜] X)
    (s : ℕ → ℕ) (hs : StrictMono s) (φ : ℕ → (X →L[𝕜] 𝕜))
    (hφ : ∀ i, ‖φ i‖ ≤ 1) {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε)
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : Summable w) (hbudget : ∑' j, w j ≤ ε)
    (hdiag : ∀ i, γ ≤ ‖φ i (R (cZeroUnit 𝕜 (s i)))‖)
    (hoff : ∀ i j, i ≠ j → ‖φ i (R (cZeroUnit 𝕜 (s j)))‖ ≤ w j)
    (a : cZero 𝕜) :
    (γ - ε) * ‖a‖ ≤ ‖R (cZeroSubsequenceInsertion s hs a)‖ := by
  classical
  let V := cZeroSubsequenceInsertion (𝕜 := 𝕜) s hs
  have hrow (i : ℕ) : γ * ‖a i‖ ≤ ‖R (V a)‖ + ε * ‖a‖ := by
    let f (j : ℕ) := a j * φ i (R (cZeroUnit 𝕜 (s j)))
    let d (j : ℕ) := if j = i then 0 else f j
    have hd (j : ℕ) : ‖d j‖ ≤ ‖a‖ * w j := by
      by_cases hji : j = i
      · subst j
        simp only [d, if_pos rfl, norm_zero]
        exact mul_nonneg (norm_nonneg _) (hw i)
      · simp only [d, hji, if_false, f, norm_mul]
        exact mul_le_mul (norm_CZero_apply_le a j) (hoff i j (Ne.symm hji))
          (norm_nonneg _) (norm_nonneg _)
    have hds : Summable (fun j => ‖d j‖) :=
      (hsum.mul_left ‖a‖).of_nonneg_of_le (fun _ => norm_nonneg _) hd
    have htail : ‖∑' j, d j‖ ≤ ε * ‖a‖ := by
      calc
        _ ≤ ∑' j, ‖d j‖ := norm_tsum_le_tsum_norm hds
        _ ≤ ∑' j, ‖a‖ * w j := hds.tsum_le_tsum hd (hsum.mul_left ‖a‖)
        _ = ‖a‖ * (∑' j, w j) := tsum_mul_left
        _ ≤ ‖a‖ * ε := mul_le_mul_of_nonneg_left hbudget (norm_nonneg _)
        _ = ε * ‖a‖ := mul_comm _ _
    have hseries : Summable f := by
      have h := (summable_smul_disjoint (fun j => cZeroUnit 𝕜 (s j))
        (cZero_subsequenceUnits_norm_le s) (cZero_subsequenceUnits_disjoint s hs) a).map
        ((φ i).comp R) ((φ i).comp R).continuous
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul] using h
    have hfull : φ i (R (V a)) = f i + ∑' j, d j := by
      change ((φ i).comp R) (∑' j, a j • cZeroUnit 𝕜 (s j)) = _
      rw [((φ i).comp R).map_tsum (summable_smul_disjoint _
        (cZero_subsequenceUnits_norm_le s) (cZero_subsequenceUnits_disjoint s hs) a)]
      simp only [map_smul, ContinuousLinearMap.comp_apply, smul_eq_mul]
      exact hseries.tsum_eq_add_tsum_ite i
    have htri : ‖f i‖ ≤ ‖φ i (R (V a))‖ + ‖∑' j, d j‖ := by
      rw [hfull]
      calc
        _ = ‖(f i + ∑' j, d j) - ∑' j, d j‖ := by simp
        _ ≤ ‖f i + ∑' j, d j‖ + ‖∑' j, d j‖ := norm_sub_le _ _
    have hnorm : ‖φ i (R (V a))‖ ≤ ‖R (V a)‖ := by
      exact ((φ i).le_opNorm _).trans (by
        simpa using mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg (R (V a))))
    have hdiag' : γ * ‖a i‖ ≤ ‖f i‖ := by
      dsimp [f]
      rw [norm_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hdiag i) (norm_nonneg (a i))
    exact hdiag'.trans (htri.trans (add_le_add hnorm htail))
  have hnorma : ‖a‖ ≤ (‖R (V a)‖ + ε * ‖a‖) / γ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro i
    exact (le_div_iff₀ hγ).mpr (by simpa [mul_comm] using hrow i)
  have h := (le_div_iff₀ hγ).mp hnorma
  change (γ - ε) * ‖a‖ ≤ ‖R (V a)‖
  nlinarith

end JLMS
