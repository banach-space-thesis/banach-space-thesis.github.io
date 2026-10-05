import ThesisCommon.Analysis.L1AdjointOneKernel

/-! The actual adjoint-at-one gives the sharp column criterion for the
norm of a positive L1 operator plus a positive integral operator. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]
variable {S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} {k : X × Y → ℝ}

theorem positiveAdjointOne_add_integral_eq_column_ae
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hk : IsIntegralKernel k K) :
    positiveAdjointOne (S + K) (add_nonneg hS hK) =ᵐ[μ]
      fun x => positiveAdjointOneDensity S hS x + ∫ y, k (x, y) ∂ν := by
  rw [positiveAdjointOne_add S K hS hK]
  filter_upwards [Lp.coeFn_add (positiveAdjointOne S hS) (positiveAdjointOne K hK),
    positiveAdjointOne_coe S hS, hk.positiveAdjointOne_eq_column_ae hK] with x h1 h2 h3
  simp only [h1, Pi.add_apply, h2, h3]

theorem norm_positive_add_integral_le_iff
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hk : IsIntegralKernel k K) {C : ℝ} (hC : 0 ≤ C) :
    ‖S + K‖ ≤ C ↔ ∀ᵐ x ∂μ,
      positiveAdjointOneDensity S hS x + (∫ y, k (x, y) ∂ν) ≤ C := by
  have heq := positiveAdjointOne_add_integral_eq_column_ae hS hK hk
  constructor
  · intro hnorm
    filter_upwards [heq, linfty_ae_norm_le_norm (positiveAdjointOne (S + K) (add_nonneg hS hK))]
      with x hx hb
    rw [norm_positiveAdjointOne] at hb
    rw [← hx]
    exact (le_abs_self _).trans (hb.trans hnorm)
  · intro hb
    rw [← norm_positiveAdjointOne (S + K) (add_nonneg hS hK)]
    apply linfty_norm_le_of_ae_bound _ hC
    filter_upwards [heq, hb, (Lp.coeFn_nonneg _).mpr
      (positiveAdjointOne_nonneg (S + K) (add_nonneg hS hK))] with x hx hb hp
    rw [Real.norm_of_nonneg hp, hx]
    exact hb

theorem positive_integral_tail_mass_le_norm
    (hS : 0 ≤ S) (hk : IsIntegralKernel k K) (hpos : ∀ z, 0 ≤ k z) (r : ℝ) :
    ∀ᵐ x ∂μ, positiveAdjointOneDensity S hS x +
      (∫ y, ‖truncatedKernel r k (x, y)‖ ∂ν) ≤ ‖S + hk.truncatedOperator r‖ := by
  have htrpos : ∀ z, 0 ≤ truncatedKernel r k z :=
    fun z => indicator_nonneg (fun w _ => hpos w) z
  have htr : 0 ≤ hk.truncatedOperator r :=
    (hk.truncatedOperator_represents r).positive_of_nonneg_ae (Eventually.of_forall htrpos)
  have hb := (norm_positive_add_integral_le_iff hS htr (hk.truncatedOperator_represents r)
    (norm_nonneg _)).mp le_rfl
  simpa only [Real.norm_of_nonneg (htrpos _)] using hb

end ThesisCommon
