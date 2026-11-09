import SurveyStatements.P5HaarBiorthogonal
import Mathlib.MeasureTheory.Function.L2Space

/-! The actual dyadic Rademacher vectors are orthonormal in real L2.
Their finite sums have squared L2 norm equal to the number of summands;
these vectors supply quantitative tests for the Capon projection. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace SurveyStatements.P5

theorem realDyadicHaar_inner (I J : DyadicIndex) :
    ⟪dyadicHaar ℝ 2 I, dyadicHaar ℝ 2 J⟫ =
      if I = J then unitIntervalMeasure.real (dyadicInterval I) else 0 := by
  have hc : dyadicHaarCoordinate ℝ 2 I (dyadicHaar ℝ 2 J) =
      (unitIntervalMeasure.real (dyadicInterval I))⁻¹ *
        ⟪dyadicHaar ℝ 2 I, dyadicHaar ℝ 2 J⟫ := by
    rw [dyadicHaarCoordinate, P5Support.lpHaarCoefficient_apply,
      dyadicChildren_union, L2.inner_def]
    congr 1
    apply integral_congr_ae
    have hcoe : dyadicHaar ℝ 2 I =ᵐ[unitIntervalMeasure]
        P5Support.lpHaarFunction ℝ (dyadicLeft I) (dyadicRight I) :=
      P5Support.lpHaarVector_coe _ _ measurableSet_Ico measurableSet_Ico
    filter_upwards [hcoe] with x hx
    simp [hx, RCLike.inner_apply, mul_comm]
  have hm : unitIntervalMeasure.real (dyadicInterval I) ≠ 0 := by
    rw [dyadicInterval_real_measure]
    positivity
  have he : ⟪dyadicHaar ℝ 2 I, dyadicHaar ℝ 2 J⟫ =
      unitIntervalMeasure.real (dyadicInterval I) *
        dyadicHaarCoordinate ℝ 2 I (dyadicHaar ℝ 2 J) := by
    rw [hc]
    field_simp
  rw [he, dyadicHaarCoordinate_biorthogonal (by norm_num)]
  split_ifs <;> simp

def dyadicRademacherL2 (n : ℕ) : Lp ℝ 2 unitIntervalMeasure :=
  ∑ k : Fin (2 ^ n), dyadicHaar ℝ 2 ⟨n, k⟩

theorem dyadicRademacherL2_inner (n m : ℕ) :
    ⟪dyadicRademacherL2 n, dyadicRademacherL2 m⟫ = if n = m then 1 else 0 := by
  rw [dyadicRademacherL2, dyadicRademacherL2, sum_inner]
  simp_rw [inner_sum, realDyadicHaar_inner]
  by_cases hnm : n = m
  · subst m
    simp [dyadicInterval_real_measure, Sigma.mk.inj_iff]
  · rw [if_neg hnm]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    exact if_neg (fun h => hnm (congrArg Sigma.fst h))

theorem norm_dyadicRademacherL2_sum_sq (N : ℕ) :
    ‖∑ n ∈ Finset.range N, dyadicRademacherL2 n‖ ^ 2 = (N : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, dyadicRademacherL2_inner]
  simp [Finset.filter_true_of_mem, Finset.mem_range]

end SurveyStatements.P5
