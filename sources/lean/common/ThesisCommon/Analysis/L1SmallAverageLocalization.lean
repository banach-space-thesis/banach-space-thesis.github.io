import ThesisCommon.Analysis.L1AdjointOneBands
import ThesisCommon.Analysis.LebesgueLpRestrictionAlgebra

/-! A small average of the actual positive adjoint density supplies a
positive-measure input band on which the operator norm is small. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

theorem positiveL1_small_average_localization
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (A : Set X) (hA : MeasurableSet A) (hpos : 0 < μ A)
    (c : ℝ) (hc : 0 ≤ c)
    (hsmall : ‖S (lOneIndicator μ A hA)‖ < c * μ.real A) :
    ∃ D : Set X, D ⊆ A ∧ ∃ hD : MeasurableSet D, 0 < μ D ∧
      ‖S.comp (lpCutL D hD)‖ ≤ c := by
  let g := positiveAdjointOneDensity S hS
  let D : Set X := A ∩ {x | g x ≤ c}
  have hg : Measurable g := measurable_positiveAdjointOneDensity S hS
  have hD : MeasurableSet D := hA.inter (measurableSet_le hg measurable_const)
  have hd : 0 < μ D := by
    by_contra hn
    have hz : μ D = 0 := le_antisymm (le_of_not_gt hn) (zero_le _)
    have ha : ∀ᵐ x ∂μ, x ∉ D := measure_eq_zero_iff_ae_notMem.mp hz
    have hbound : ∀ᵐ x ∂μ.restrict A, c ≤ g x := by
      filter_upwards [ae_restrict_of_ae ha, ae_restrict_mem hA] with x hx hxA
      have hnle : ¬ g x ≤ c := fun h => hx ⟨hxA, h⟩
      exact (lt_of_not_ge hnle).le
    have hi : c * μ.real A ≤ ∫ x in A, g x ∂μ := by
      have h := integral_mono_ae
        (integrable_const c : Integrable (fun _ : X => c) (μ.restrict A))
        ((positiveAdjointOneDensity_memLp S hS).integrable le_top).integrableOn hbound
      simpa only [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
        univ_inter, smul_eq_mul, mul_comm] using h
    have he : (∫ x in A, g x ∂μ) = ‖S (lOneIndicator μ A hA)‖ := by
      rw [positiveAdjointOneDensity_indicator,
        lOne_norm_eq_integral_of_nonneg _ (hS _ (lOneIndicator_nonneg A hA))]
    exact (not_lt_of_ge (he ▸ hi)) hsmall
  refine ⟨D, inter_subset_left, hD, hd, ?_⟩
  apply (norm_positive_le_iff_adjointDensity (positive_inputCut_nonneg hS D hD) hc).mpr
  filter_upwards [positiveAdjointOneDensity_inputCut hS D hD] with x hx
  rw [hx]
  by_cases hxD : x ∈ D
  · simpa only [indicator_of_mem hxD] using hxD.2
  · simpa only [indicator_of_notMem hxD] using hc

end ThesisCommon
