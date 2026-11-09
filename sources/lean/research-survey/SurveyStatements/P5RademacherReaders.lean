import SurveyStatements.P5BoundedScalarReaders

/-! Actual bounded Rademacher integration readers, with their exact values
on Haar vectors and Rademacher levels at any admissible Lp exponent. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal BigOperators RealInnerProductSpace

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem dyadicRademacherFunction_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (dyadicRademacherFunction ℝ n) := by
  unfold dyadicRademacherFunction
  apply Finset.stronglyMeasurable_fun_sum
  intro k _
  exact (stronglyMeasurable_const.indicator measurableSet_Ioc).sub
    (stronglyMeasurable_const.indicator measurableSet_Ioc)

def rademacherReader (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    Lp ℝ p unitIntervalMeasure →L[ℝ] ℝ :=
  boundedScalarReader (dyadicRademacherFunction ℝ n)
    (dyadicRademacherFunction_stronglyMeasurable n)
    (norm_dyadicRademacherFunction_le n)

theorem norm_rademacherReader_le (n : ℕ) : ‖rademacherReader p n‖ ≤ 1 :=
  norm_boundedScalarReader_le _ _ _

theorem rademacherReader_apply (n : ℕ) (f : Lp ℝ p unitIntervalMeasure) :
    rademacherReader p n f =
      ∫ x, dyadicRademacherFunction ℝ n x * f x ∂unitIntervalMeasure :=
  boundedScalarReader_apply _ _ _ _

theorem dyadicHaar_ae_change_exponent {q : ℝ≥0∞} [Fact (1 ≤ q)] (I : DyadicIndex) :
    dyadicHaar ℝ p I =ᵐ[unitIntervalMeasure] dyadicHaar ℝ q I := by
  exact (P5Support.lpHaarVector_coe _ _ measurableSet_Ico measurableSet_Ico).trans
    (P5Support.lpHaarVector_coe _ _ measurableSet_Ico measurableSet_Ico).symm

theorem rademacherReader_dyadicHaar (n : ℕ) (I : DyadicIndex) :
    rademacherReader p n (dyadicHaar ℝ p I) =
      if n = I.1 then unitIntervalMeasure.real (dyadicInterval I) else 0 := by
  rw [rademacherReader_apply]
  have he : (fun x => dyadicRademacherFunction ℝ n x * dyadicHaar ℝ p I x)
      =ᵐ[unitIntervalMeasure] fun x =>
        ⟪dyadicRademacherL2 n x, dyadicHaar ℝ 2 I x⟫ := by
    filter_upwards [(dyadicRademacherLp_ae (𝕜 := ℝ) (p := 2) n),
      dyadicHaar_ae_change_exponent (p := p) (q := 2) I] with x hn hI
    change dyadicRademacherL2 n x = _ at hn
    rw [← hn, hI]
    simp [RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae he, ← L2.inner_def, dyadicRademacherL2, sum_inner]
  simp_rw [realDyadicHaar_inner]
  by_cases hn : n = I.1
  · subst n
    rcases I with ⟨m, k⟩
    simp [Sigma.mk.inj_iff]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro k _
    exact if_neg (fun h => hn (congrArg Sigma.fst h))

theorem rademacherReader_level (n m : ℕ) :
    rademacherReader p n (dyadicRademacherLp ℝ p m) = if n = m then 1 else 0 := by
  rw [dyadicRademacherLp, map_sum]
  simp_rw [rademacherReader_dyadicHaar]
  by_cases hnm : n = m
  · subst m
    simp [dyadicInterval_real_measure]
  · simp [hnm]

end SurveyStatements.P5
