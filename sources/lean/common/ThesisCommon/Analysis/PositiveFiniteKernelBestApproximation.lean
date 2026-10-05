import ThesisCommon.Analysis.L1AdjointOneNormCriterion
import ThesisCommon.Analysis.PositiveKernelClipping

/-! Positive budget clipping on arbitrary finite real measure spaces.
The budget is derived from the actual adjoint-at-one density. Its column
criterion bounds the genuine error operator, so no topological model or
reverse-kernel representation is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem exists_positive_weaklyCompact_truncationInf_approx_finite_of_nonneg_kernel
    (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    {k : X × Y → ℝ} (hk : IsIntegralKernel k K) (hpos : ∀ z, 0 ≤ k z) :
    ∃ H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, IsWeaklyCompactOperator H ∧
      0 ≤ H ∧ H ≤ K ∧ ‖S + K - H‖ ≤
        sInf (Set.range (fun n : ℕ => ‖S + hk.truncatedOperator n‖)) := by
  let q : ℕ → ℝ := fun n => ‖S + hk.truncatedOperator n‖
  let c : ℝ := sInf (Set.range q)
  let g : X → ℝ := positiveAdjointOneDensity S hS
  let d : X → ℝ := fun x => c - g x
  have hc : 0 ≤ c := le_csInf (Set.range_nonempty _) (by
    rintro _ ⟨n, rfl⟩
    exact norm_nonneg _)
  have hdmeas : Measurable d := measurable_const.sub (measurable_positiveAdjointOneDensity S hS)
  have hgle : ∀ᵐ x ∂μ, g x ≤ c := by
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g x ≤ q n := by
      apply eventually_countable_forall.mpr
      intro n
      filter_upwards [positive_integral_tail_mass_le_norm hS hk hpos n] with x hx
      have hnn : 0 ≤ ∫ y, ‖truncatedKernel n k (x, y)‖ ∂ν :=
        integral_nonneg fun y => norm_nonneg _
      dsimp only [g, q]
      linarith
    filter_upwards [hall] with x hx
    exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨n, rfl⟩; exact hx n)
  have hd0 : ∀ᵐ x ∂μ, 0 ≤ d x := hgle.mono fun x hx => sub_nonneg.mpr hx
  let H := hk.budgetClippedOperator hdmeas
  have hweak : IsWeaklyCompactOperator H := by
    apply hk.weaklyCompact_budgetClippedOperator hdmeas hd0
    intro ε hε
    obtain ⟨r, ⟨n, rfl⟩, hn⟩ := exists_lt_of_csInf_lt (Set.range_nonempty q)
      (show sInf (Set.range q) < c + ε from lt_add_of_pos_right c hε)
    refine ⟨n, ?_⟩
    filter_upwards [positive_integral_tail_mass_le_norm hS hk hpos n,
      hk.clipResidualMass_le_truncatedKernel n] with x hx hRx
    apply max_le _ hε.le
    dsimp only [d, g]
    change ‖S + hk.truncatedOperator n‖ < c + ε at hn
    linarith
  have hH : 0 ≤ H := (hk.isIntegralKernel_budgetClippedOperator hdmeas).positive_of_nonneg_ae
    (Eventually.of_forall fun z => budgetClipKernel_nonneg hpos d z)
  have hHK : H ≤ K := sub_nonneg.mp
    ((hk.sub (hk.isIntegralKernel_budgetClippedOperator hdmeas)).positive_of_nonneg_ae
      (Eventually.of_forall fun z => sub_nonneg.mpr (budgetClipKernel_le_self hpos d z)))
  refine ⟨H, hweak, hH, hHK, ?_⟩
  rw [show S + K - H = S + (K - H) by abel]
  apply (norm_positive_add_integral_le_iff hS (sub_nonneg.mpr hHK)
    (hk.sub (hk.isIntegralKernel_budgetClippedOperator hdmeas)) hc).mpr
  filter_upwards [hk.budgetClippedKernel_error hd0] with x he
  have hnorm : ∀ y, ‖k (x, y) - budgetClipKernel ν k d (x, y)‖ =
      k (x, y) - budgetClipKernel ν k d (x, y) := fun y =>
    Real.norm_of_nonneg (sub_nonneg.mpr (budgetClipKernel_le_self hpos d (x, y)))
  simp only [hnorm] at he
  rw [he]
  have hm := min_le_right (∫ y, ‖k (x, y)‖ ∂ν) (d x)
  dsimp only [d, g] at hm
  linarith

theorem exists_positive_weaklyCompact_truncationInf_approx_finite
    (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hK : 0 ≤ K)
    {k : X × Y → ℝ} (hk : IsIntegralKernel k K) :
    ∃ H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, IsWeaklyCompactOperator H ∧
      0 ≤ H ∧ H ≤ K ∧ ‖S + K - H‖ ≤
        sInf (Set.range (fun n : ℕ => ‖S + hk.truncatedOperator n‖)) := by
  have ha : IsIntegralKernel (fun z => |k z|) K := by
    simpa only [abs_of_nonneg hK] using hk.abs
  obtain ⟨H, hH, hpos, hHK, hnorm⟩ :=
    exists_positive_weaklyCompact_truncationInf_approx_finite_of_nonneg_kernel
      S K hS ha (fun z => abs_nonneg (k z))
  refine ⟨H, hH, hpos, hHK, ?_⟩
  have htr : ∀ r : ℝ, ha.truncatedOperator r = hk.truncatedOperator r := by
    intro r
    apply ((ha.truncatedOperator_represents r).congr_ae
      (measurable_truncatedKernel hk.measurable r) ?_).unique (hk.truncatedOperator_represents r)
    filter_upwards [ha.kernel_unique hk] with z hz
    simp only [truncatedKernel, Set.indicator_apply, Set.mem_setOf_eq, hz]
  simpa only [htr] using hnorm

theorem exists_positive_weaklyCompact_integralBand_truncationInf_approx_finite
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T)
    {k : X × Y → ℝ} (hk : IsIntegralKernel k (integralBandProjection T)) :
    ∃ H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, IsWeaklyCompactOperator H ∧
      0 ≤ H ∧ H ≤ integralBandProjection T ∧ ‖T - H‖ ≤
        sInf (Set.range (fun n : ℕ =>
          ‖T - integralBandProjection T + hk.truncatedOperator n‖)) := by
  have hS : 0 ≤ T - integralBandProjection T :=
    sub_nonneg.mpr (integralBandProjection_le_id T hT)
  have hK : 0 ≤ integralBandProjection T := integralBandProjection_nonneg T hT
  simpa only [sub_add_cancel] using exists_positive_weaklyCompact_truncationInf_approx_finite
    (T - integralBandProjection T) (integralBandProjection T) hS hK hk

end ThesisCommon
