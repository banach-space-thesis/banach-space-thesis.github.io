import ThesisCommon.Analysis.Cotype
import ThesisCommon.Analysis.SignAveraging
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Exact Rademacher second moments, and hence cotype two with constant
one, in real and complex inner-product spaces. All finite sign averages
use the same convention as the preservation theorems. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem re_inner_signedValue (b c : Bool) (x y : H) :
    RCLike.re (inner 𝕜 (signedValue b x) (signedValue c y)) =
      signedValue b (signedValue c (RCLike.re (inner 𝕜 x y))) := by
  cases b <;> cases c <;> simp [signedValue, inner_neg_left, inner_neg_right]

include 𝕜

theorem sign_average_norm_sq (x : ι → H) :
    (∑ θ : ι → Bool, ‖∑ i, signedValue (θ i) (x i)‖ ^ (2 : ℕ)) =
      (Fintype.card (ι → Bool) : ℝ) * ∑ i, ‖x i‖ ^ (2 : ℕ) := by
  calc
    _ = ∑ θ : ι → Bool, ∑ i, ∑ j,
        RCLike.re (inner 𝕜 (signedValue (θ i) (x i)) (signedValue (θ j) (x j))) := by
      simp_rw [@norm_sq_eq_re_inner 𝕜, sum_inner, inner_sum, map_sum]
    _ = ∑ i, ∑ j, ∑ θ : ι → Bool,
        RCLike.re (inner 𝕜 (signedValue (θ i) (x i)) (signedValue (θ j) (x j))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i, (Fintype.card (ι → Bool) : ℝ) * ‖x i‖ ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp_rw [← @norm_sq_eq_re_inner 𝕜, norm_signedValue]
        simp
      · intro j hj hji
        simp_rw [re_inner_signedValue]
        exact signed_correlation_sum_zero hji.symm _
      · simp
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem innerProduct_hasRademacherCotype_two : HasRademacherCotype H 2 1 := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  intro n x
  have h := sign_average_norm_sq (𝕜 := 𝕜) x
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ)^n := by simp
  rw [hcard] at h
  simp only [Real.rpow_two, one_pow, one_mul]
  change (∑ i, ‖x i‖ ^ (2 : ℕ)) ≤ (2 ^ n : ℝ)⁻¹ *
    ∑ θ : Fin n → Bool, ‖∑ i, signedValue (θ i) (x i)‖ ^ (2 : ℕ)
  rw [h, ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 ^ n : ℝ) ≠ 0), one_mul]

theorem innerProduct_hasFiniteCotype : HasFiniteCotype H :=
  ⟨2, 1, innerProduct_hasRademacherCotype_two (𝕜 := 𝕜)⟩

end ThesisCommon
