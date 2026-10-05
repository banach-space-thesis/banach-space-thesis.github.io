import ThesisCommon.Analysis.KernelTailRemainder
import ThesisCommon.Analysis.KernelOperatorNorm
import ThesisCommon.Analysis.PositiveOperatorKernelParts
import ThesisCommon.Analysis.IntegralKernelApproximation

/-! The converse quantitative truncation bound for positive operators on
the standard compact models. Countable algebra tests replace pointwise
neighborhood arguments, including singular fibres and atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem norm_singular_truncated_le_of_smallCuts
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure T hT)
    (hk : IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection T))
    {δ C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hTr : ‖T‖ / r < δ)
    (hcut : ∀ (B : Set Y) (hB : MeasurableSet B), ν.real B < δ →
      ‖(lpCutL B hB).comp T‖ ≤ C) :
    ‖T - integralBandProjection T + hk.truncatedOperator r‖ ≤ C := by
  have hs : 0 ≤ T - integralBandProjection T :=
    sub_nonneg.mpr (integralBandProjection_le_id T hT)
  have ht : 0 ≤ hk.truncatedOperator r :=
    (hk.truncatedOperator_represents r).positive_of_nonneg_ae
      (Eventually.of_forall fun z => indicator_nonneg
        (fun w _ => kernelRealDensity_nonneg κ ν w) z)
  have hprod : μ ⊗ₘ kernelTailRemainder κ ν r =
      clopenOperatorMeasure (T - integralBandProjection T + hk.truncatedOperator r)
        (add_nonneg hs ht) := by
    rw [compProd_kernelTailRemainder,
      compProd_kernelSingularPart_eq_operator_residual T hT κ hrepr,
      clopenOperatorMeasure_add _ _ hs ht,
      (hk.truncatedOperator_represents r).clopenOperatorMeasure_eq ht]
    rfl
  apply (positive_operator_norm_le_iff_kernel_mass _ (add_nonneg hs ht)
    (kernelTailRemainder κ ν r) hprod C hC).mpr
  have hmass : ∀ᵐ x ∂μ, (κ x).real univ ≤ ‖T‖ := by
    have h := (positive_operator_norm_le_iff_kernel_mass T hT κ hrepr ‖T‖
      (norm_nonneg T)).mp le_rfl
    exact h.mono fun x hx => ENNReal.toReal_le_of_le_ofReal (norm_nonneg T) hx
  have hb := ae_kernelTailRemainder_mass_bound κ ν hr hTr hmass
    (fun B hB hδ => (positive_operator_outputCut_norm_le_iff_kernel_real_mass
      T hT κ hrepr B hB C hC).mp (hcut B hB hδ))
  exact hb.mono fun x hx =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hC).mpr hx

theorem exists_nat_truncated_remainder_le_of_smallCuts
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure T hT)
    (hk : IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection T))
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcut : ∀ (B : Set Y) (hB : MeasurableSet B), ν.real B < δ →
      ‖(lpCutL B hB).comp T‖ ≤ C) :
    ∃ n : ℕ, ‖T - integralBandProjection T + hk.truncatedOperator n‖ ≤ C := by
  obtain ⟨n, hn⟩ := exists_nat_gt (‖T‖ / δ + 1)
  have hdiv : 0 ≤ ‖T‖ / δ := div_nonneg (norm_nonneg T) hδ.le
  have hnpos : 0 < (n : ℝ) := by linarith
  have hratio : ‖T‖ / (n : ℝ) < δ := by
    apply (div_lt_iff₀ hnpos).mpr
    have hmul := mul_lt_mul_of_pos_right hn hδ
    rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at hmul
    nlinarith
  exact ⟨n, norm_singular_truncated_le_of_smallCuts T hT κ hrepr hk hC hnpos hratio hcut⟩

end ThesisCommon
