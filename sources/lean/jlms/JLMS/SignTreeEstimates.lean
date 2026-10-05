import JLMS.SignTreeLower

/-!
# Finite averaging and near-sign estimates for Hagler–Johnson

A nearly maximal average forces every summand to be nearly maximal. Applied
to half-differences this gives opposite signs. A small norm excess and a
near-extremal real part then give a scalar value within 1/4 of the desired
sign, including for complex scalars.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finite_average_each_lower {I : Type*} [DecidableEq I] (F : Finset I)
    (a : I → ℝ) {ε : ℝ} (hupper : ∀ i ∈ F, a i ≤ 1 + ε)
    (hlower : (F.card : ℝ) * (1 - ε) ≤ ∑ i ∈ F, a i) {i : I} (hi : i ∈ F) :
    (F.card : ℝ) * (1 - ε) - ((F.card : ℝ) - 1) * (1 + ε) ≤ a i := by
  have hrest : ∑ j ∈ F.erase i, a j ≤ (F.erase i).card * (1 + ε) := by
    calc
      _ ≤ ∑ j ∈ F.erase i, (1 + ε) := Finset.sum_le_sum (fun j hj => hupper j (Finset.mem_of_mem_erase hj))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((F.erase i).card : ℝ) + 1 = (F.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one hi
  have hsum := Finset.sum_erase_add F a hi
  have hcard' := congrArg (fun t : ℝ => t * (1 + ε)) hcard
  nlinarith

theorem finite_average_sign_margin {I : Type*} [DecidableEq I] (F : Finset I)
    (a : I → ℝ) {ε u : ℝ} (hε : 0 ≤ ε)
    (hsmall : 2 * (F.card : ℝ) * ε ≤ u)
    (hupper : ∀ i ∈ F, a i ≤ 1 + ε)
    (hlower : (F.card : ℝ) * (1 - ε) ≤ ∑ i ∈ F, a i) {i : I} (hi : i ∈ F) :
    1 - u ≤ a i := by
  have h := finite_average_each_lower F a hupper hlower hi
  nlinarith

theorem half_difference_opposite_signs (z w : 𝕜) {ε u : ℝ}
    (hz : ‖z‖ ≤ 1 + ε) (hw : ‖w‖ ≤ 1 + ε)
    (hdiff : 1 - u ≤ (RCLike.re z - RCLike.re w) / 2) :
    1 - (2 * u + ε) ≤ RCLike.re z ∧ RCLike.re w ≤ -1 + (2 * u + ε) := by
  have hrz := RCLike.re_le_norm z
  have hrw : -(1 + ε) ≤ RCLike.re w := by
    have h := (abs_le.mp (RCLike.abs_re_le_norm w)).1
    linarith
  constructor <;> linarith

theorem norm_sub_one_sq (z : 𝕜) : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * RCLike.re z + 1 := by
  rw [RCLike.norm_sq_eq_def (z := z - 1), RCLike.norm_sq_eq_def (z := z)]
  simp only [map_sub, RCLike.one_re, RCLike.one_im, sub_zero]
  ring

theorem norm_near_positive_sign (z : 𝕜)
    (hn : ‖z‖ ≤ 1 + (1 / 1024 : ℝ)) (hr : 1 - (3 / 1024 : ℝ) ≤ RCLike.re z) :
    ‖z - 1‖ ≤ 1 / 4 := by
  have hsq : ‖z‖ ^ 2 ≤ (1 + (1 / 1024 : ℝ)) ^ 2 := by
    nlinarith [norm_nonneg z]
  have heq := norm_sub_one_sq z
  nlinarith [norm_nonneg (z - 1)]

theorem norm_near_negative_sign (z : 𝕜)
    (hn : ‖z‖ ≤ 1 + (1 / 1024 : ℝ)) (hr : RCLike.re z ≤ -1 + (3 / 1024 : ℝ)) :
    ‖z - (-1)‖ ≤ 1 / 4 := by
  have h := norm_near_positive_sign (-z) (by simpa using hn) (by simp only [map_neg]; linarith)
  have heq : -z - 1 = -(z - (-1)) := by ring
  simpa only [heq, norm_neg] using h

end JLMS
