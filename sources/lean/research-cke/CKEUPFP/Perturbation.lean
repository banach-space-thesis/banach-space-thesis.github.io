import CKEUPFP.Definitions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The quantitative perturbation step

This is the Neumann-series argument at the end of Section 4. The inverse is
constructed from a convergent geometric series, and its norm bound is proved.
-/

noncomputable section

universe u v w z

namespace CKEUPFP

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {E : Type z} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A perturbation within `1/4` of the identity has a two-sided inverse with
operator norm at most `4/3`, including the zero-space case. -/
theorem exists_inverse_of_norm_sub_id_le_quarter (G : E →L[𝕜] E)
    (hG : ‖G - ContinuousLinearMap.id 𝕜 E‖ ≤ (1 / 4 : ℝ)) :
    ∃ H : E →L[𝕜] E,
      H.comp G = ContinuousLinearMap.id 𝕜 E ∧
      G.comp H = ContinuousLinearMap.id 𝕜 E ∧ ‖H‖ ≤ (4 / 3 : ℝ) := by
  change ‖G - 1‖ ≤ (1 / 4 : ℝ) at hG
  let d : E →L[𝕜] E := 1 - G
  have hdquarter : ‖d‖ ≤ (1 / 4 : ℝ) := by
    simpa only [d, norm_sub_rev] using hG
  have hd : ‖d‖ < 1 := lt_of_le_of_lt hdquarter (by norm_num)
  let a := Units.oneSub d hd
  let H : E →L[𝕜] E := a.inv
  have ha : a.val = G := by simp [a, d]
  have hleft : H.comp G = ContinuousLinearMap.id 𝕜 E := by
    change a.inv * G = 1
    rw [← ha]
    exact a.inv_val
  have hright : G.comp H = ContinuousLinearMap.id 𝕜 E := by
    change G * a.inv = 1
    rw [← ha]
    exact a.val_inv
  have hinv : (1 - ‖d‖)⁻¹ ≤ (4 / 3 : ℝ) := by
    calc
      (1 - ‖d‖)⁻¹ = 1 / (1 - ‖d‖) := (one_div _).symm
      _ ≤ 1 / (3 / 4 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ = (4 / 3 : ℝ) := by norm_num
  have hnormone : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hnorm : ‖H‖ ≤ (4 / 3 : ℝ) := by
    change ‖∑' n : ℕ, d ^ n‖ ≤ (4 / 3 : ℝ)
    have hs := tsum_geometric_le_of_norm_lt_one d hd
    linarith
  exact ⟨H, hleft, hright, hnorm⟩

/-- Correct an approximate identity factorisation to an exact one, with the
same `4/3` loss used in the paper. -/
theorem factorsThroughWith_id_of_approximate
    (T : X →L[𝕜] Y) (U : Y →L[𝕜] E) (V : E →L[𝕜] X)
    (h : ‖(U.comp T).comp V - ContinuousLinearMap.id 𝕜 E‖ ≤ (1 / 4 : ℝ)) :
    FactorsThroughWith (ContinuousLinearMap.id 𝕜 E) T
      ((4 / 3 : ℝ) * (‖U‖ * ‖V‖)) := by
  obtain ⟨H, hH, _, hnormH⟩ :=
    exists_inverse_of_norm_sub_id_le_quarter ((U.comp T).comp V) h
  refine ⟨H.comp U, V, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using hH
  · calc
      ‖H.comp U‖ * ‖V‖ ≤ (‖H‖ * ‖U‖) * ‖V‖ :=
        mul_le_mul_of_nonneg_right (H.opNorm_comp_le U) (norm_nonneg V)
      _ ≤ ((4 / 3 : ℝ) * ‖U‖) * ‖V‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnormH (norm_nonneg U)) (norm_nonneg V)
      _ = (4 / 3 : ℝ) * (‖U‖ * ‖V‖) := mul_assoc _ _ _

omit [CompleteSpace E] in
/-- The multiplier-compression error has the product norm bound used in
Section 4. No field measurability or selection statement is assumed here. -/
theorem sandwiched_error_le (L R S A : E →L[𝕜] E)
    (hA : (L.comp A).comp R = ContinuousLinearMap.id 𝕜 E) :
    ‖(L.comp S).comp R - ContinuousLinearMap.id 𝕜 E‖ ≤
      ‖L‖ * ‖S - A‖ * ‖R‖ := by
  rw [← hA]
  have he : (L.comp S).comp R - (L.comp A).comp R = (L.comp (S - A)).comp R := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  rw [he]
  exact ((L.comp (S - A)).opNorm_comp_le R).trans
    (mul_le_mul_of_nonneg_right (L.opNorm_comp_le (S - A)) (norm_nonneg R))

end CKEUPFP
