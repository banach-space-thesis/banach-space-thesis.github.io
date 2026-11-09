import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! The bounded-row estimate gives an actual operator into scalar ell-one.

Finite phase alignment follows the genuine proof in the adjacent
`ThesisCommon/Analysis/InfinityScalarRows.lean`; only mathlib is imported.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SurveyStatements.P2
universe v
variable {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem sum_norm_apply_le_of_unit_sums (φ : Z →L[ℂ] ℂ) (x : ℕ → Z) (C : ℝ)
    (h : ∀ (F : Finset ℕ) (a : ℕ → ℂ), (∀ j ∈ F, ‖a j‖ ≤ 1) →
      ‖∑ j ∈ F, a j • x j‖ ≤ C) (F : Finset ℕ) :
    ∑ j ∈ F, ‖φ (x j)‖ ≤ ‖φ‖ * C := by
  choose a ha hphase using fun j => RCLike.exists_norm_eq_mul_self (φ (x j))
  have heq : φ (∑ j ∈ F, a j • x j) = ((∑ j ∈ F, ‖φ (x j)‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => (hphase j).symm)
  calc
    _ = ‖φ (∑ j ∈ F, a j • x j)‖ := by
      rw [heq, Complex.norm_real,
        Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖φ‖ * ‖∑ j ∈ F, a j • x j‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * C := mul_le_mul_of_nonneg_left (h F a (fun j _ => (ha j).le)) (norm_nonneg _)

theorem bounded_row_absolute_sum_le (U : ℕ → Z →L[ℂ] Z) (C : ℝ)
    (hrow : ∀ (F : Finset ℕ) (a : ℕ → ℂ), (∀ j ∈ F, ‖a j‖ ≤ 1) →
      ‖∑ j ∈ F, a j • U j‖ ≤ C) (φ : Z →L[ℂ] ℂ) (x : Z) (F : Finset ℕ) :
    ∑ j ∈ F, ‖φ (U j x)‖ ≤ (‖φ‖ * C) * ‖x‖ := by
  rw [mul_assoc]
  apply sum_norm_apply_le_of_unit_sums φ (fun j => U j x) (C * ‖x‖)
  intro G a ha
  have happly : (∑ j ∈ G, a j • U j) x = ∑ j ∈ G, a j • U j x := by simp
  rw [← happly]
  exact ((∑ j ∈ G, a j • U j : Z →L[ℂ] Z).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hrow G a ha) (norm_nonneg x))

/-- The sequence of row coefficients is in ell-one with its genuine sum norm. -/
def rowEllOneMap (U : ℕ → Z →L[ℂ] Z) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ (F : Finset ℕ) (a : ℕ → ℂ), (∀ j ∈ F, ‖a j‖ ≤ 1) →
      ‖∑ j ∈ F, a j • U j‖ ≤ C) (φ : Z →L[ℂ] ℂ) :
    Z →L[ℂ] lp (fun _ : ℕ => ℂ) 1 := by
  let L : Z →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 1 :=
    { toFun := fun x => ⟨fun j => φ (U j x),
        memℓp_gen' (by simpa only [ENNReal.toReal_one, Real.rpow_one] using
          bounded_row_absolute_sum_le U C hrow φ x)⟩
      map_add' := by intro x y; apply lp.ext; funext j; simp
      map_smul' := by intro c x; apply lp.ext; funext j; simp }
  refine L.mkContinuous (‖φ‖ * C) ?_
  intro x
  exact lp.norm_le_of_forall_sum_le (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
    (mul_nonneg (mul_nonneg (norm_nonneg φ) hC) (norm_nonneg x))
    (f := L x) (by simpa only [ENNReal.toReal_one, Real.rpow_one] using
      bounded_row_absolute_sum_le U C hrow φ x)

@[simp] theorem rowEllOneMap_apply (U : ℕ → Z →L[ℂ] Z) (C hC hrow φ) (x : Z) (j : ℕ) :
    rowEllOneMap U C hC hrow φ x j = φ (U j x) := rfl

end SurveyStatements.P2
