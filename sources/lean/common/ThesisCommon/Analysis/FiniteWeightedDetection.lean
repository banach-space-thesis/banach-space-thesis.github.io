import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic

/-! Positive finite weighted sums preserve seminorm bounds. Genuine dual
functionals with controlled off-diagonal errors give a strict lower norm
bound on a weighted sum. These are explicit algebraic/analytic helpers,
not existence assumptions for any Gowers--Maurey operator. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]

theorem seminorm_positive_weighted_sum_le
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (p : Seminorm 𝕜 V) (w : ι → ℝ) (v : ι → V) {B : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hv : ∀ i, p (v i) ≤ B) :
    p (∑ i, (w i : 𝕜) • v i) ≤ B := by
  calc
    _ ≤ ∑ i, p ((w i : 𝕜) • v i) :=
      Finset.univ.le_sum_of_subadditive p (map_zero p) (map_add_le_add p) _
    _ = ∑ i, w i * p (v i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * B := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (hw i))
    _ = B := by rw [← Finset.sum_mul,hs,one_mul]

theorem strict_lower_bound_positive_weighted_sum
    (w a : ι → ℝ) {r : ℝ} (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ i, 0 < w i → r < a i) : r < ∑ i, w i * a i := by
  classical
  have hpos : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have hz := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    rw [hs] at hz
    linarith
  have hle (i : ι) : w i * r ≤ w i * a i := by
    rcases (hw i).eq_or_lt with hi | hi
    · rw [← hi]; simp
    · exact mul_le_mul_of_nonneg_left (ha i hi).le (hw i)
  obtain ⟨i,hi⟩ := hpos
  calc
    r = ∑ j, w j * r := by rw [← Finset.sum_mul,hs,one_mul]
    _ < _ := Finset.sum_lt_sum (fun j _ => hle j)
      ⟨i,Finset.mem_univ i,mul_lt_mul_of_pos_left (ha i hi) hi⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [DecidableEq ι]

theorem sum_functionals_apply_sub_diagonal_norm_le
    (f : ι → V →L[𝕜] 𝕜) (v : ι → V) (i : ι) {η : ℝ}
    (hcross : ∑ j ∈ Finset.univ.erase i, ‖f j (v i)‖ ≤ η) :
    ‖(∑ j, f j) (v i) - f i (v i)‖ ≤ η := by
  classical
  have he : (∑ j, f j) (v i) - f i (v i) =
      ∑ j ∈ Finset.univ.erase i, f j (v i) := by
    rw [ContinuousLinearMap.sum_apply]
    have h := Finset.sum_erase_add Finset.univ (fun j => f j (v i)) (Finset.mem_univ i)
    exact sub_eq_iff_eq_add.mpr h.symm
  rw [he]
  exact (norm_sum_le _ _).trans hcross

theorem weighted_vector_norm_gt_of_functionals
    (w : ι → ℝ) (v : ι → V) (f : ι → V →L[𝕜] 𝕜) {r η C : ℝ}
    (hC : 0 < C) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hdiag : ∀ i, 0 < w i → r+η < RCLike.re (f i (v i)))
    (hcross : ∀ i, 0 < w i → ∑ j ∈ Finset.univ.erase i, ‖f j (v i)‖ ≤ η)
    (hdual : ‖∑ i, f i‖ ≤ C) :
    r / C < ‖∑ i, (w i : 𝕜) • v i‖ := by
  classical
  let F : V →L[𝕜] 𝕜 := ∑ i, f i
  have hlocal (i : ι) (hi : 0 < w i) : r < RCLike.re (F (v i)) := by
    have herr := sum_functionals_apply_sub_diagonal_norm_le f v i (hcross i hi)
    have hreal := RCLike.re_le_norm (f i (v i)-F (v i))
    rw [map_sub,norm_sub_rev] at hreal
    have hd := hdiag i hi
    change ‖F (v i)-f i (v i)‖ ≤ η at herr
    linarith
  have heval : RCLike.re (F (∑ i, (w i : 𝕜) • v i)) =
      ∑ i, w i * RCLike.re (F (v i)) := by
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,smul_eq_mul,RCLike.re_ofReal_mul]
  have hlow : r < RCLike.re (F (∑ i, (w i : 𝕜) • v i)) := by
    rw [heval]
    exact strict_lower_bound_positive_weighted_sum w _ hw hs hlocal
  have hupper : RCLike.re (F (∑ i, (w i : 𝕜) • v i)) ≤
      C * ‖∑ i, (w i : 𝕜) • v i‖ :=
    (RCLike.re_le_norm _).trans ((F.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hdual (norm_nonneg _)))
  exact (div_lt_iff₀ hC).mpr (by nlinarith)

end ThesisCommon
