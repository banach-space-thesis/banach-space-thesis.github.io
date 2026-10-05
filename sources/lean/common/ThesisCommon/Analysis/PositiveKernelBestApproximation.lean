import ThesisCommon.Analysis.PositiveKernelClipping
import ThesisCommon.Analysis.KernelTailRemainder

/-! Construction of a positive weakly compact approximant attaining the
truncation-infimum bound. The paper's norm formula identifies this infimum
with the weak essential norm. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder

namespace ThesisCommon

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integral_norm_truncatedKernel_of_nonneg {ν : Measure Y} {k : X × Y → ℝ}
    (hk : Measurable k) (hpos : ∀ z, 0 ≤ k z) (r : ℝ) (x : X) :
    (∫ y, ‖truncatedKernel r k (x, y)‖ ∂ν) = ∫ y in {y | r ≤ k (x, y)}, k (x, y) ∂ν := by
  have heq : (fun y => ‖truncatedKernel r k (x, y)‖) =
      {y | r ≤ k (x, y)}.indicator (fun y => k (x, y)) := by
    funext y
    by_cases hr : r ≤ k (x, y)
    · have hm : (x, y) ∈ {z | r ≤ ‖k z‖} := by
        simpa only [mem_setOf_eq, Real.norm_of_nonneg (hpos (x, y))] using hr
      rw [truncatedKernel, Set.indicator_of_mem hm,
        Set.indicator_of_mem (show y ∈ {y | r ≤ k (x, y)} from hr),
        Real.norm_of_nonneg (hpos (x, y))]
    · have hm : (x, y) ∉ {z | r ≤ ‖k z‖} := by
        simpa only [mem_setOf_eq, Real.norm_of_nonneg (hpos (x, y))] using hr
      rw [truncatedKernel, Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (show y ∉ {y | r ≤ k (x, y)} from hr), norm_zero]
  rw [heq, integral_indicator]
  exact measurableSet_le measurable_const (hk.comp (measurable_const.prodMk measurable_id))

variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem positive_kernel_remainder_mass_bound
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure T hT)
    (hk : IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection T)) (r : ℝ) :
    ∀ᵐ x ∂μ, (kernelSingularPart κ ν x).real univ +
      (∫ y, ‖truncatedKernel r (kernelRealDensity κ ν) (x, y)‖ ∂ν) ≤
        ‖T - integralBandProjection T + hk.truncatedOperator r‖ := by
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
  have hb := (positive_operator_norm_le_iff_kernel_mass _ (add_nonneg hs ht)
    (kernelTailRemainder κ ν r) hprod _ (norm_nonneg _)).mp le_rfl
  filter_upwards [hb] with x hx
  have hr := ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hx
  rw [← measureReal_def, kernelTailRemainder_real_univ,
    ← integral_norm_truncatedKernel_of_nonneg (measurable_kernelRealDensity κ ν)
      (kernelRealDensity_nonneg κ ν)] at hr
  exact hr

/-- The budget construction attains the exact truncation-infimum bound, with
a positive weakly compact operator below the integral part. -/
theorem exists_positive_weaklyCompact_truncationInf_approx
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure T hT)
    (hk : IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection T)) :
    ∃ H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, IsWeaklyCompactOperator H ∧
      0 ≤ H ∧ H ≤ integralBandProjection T ∧
      ‖T - H‖ ≤ sInf (Set.range (fun n : ℕ =>
        ‖T - integralBandProjection T + hk.truncatedOperator n‖)) := by
  let q : ℕ → ℝ := fun n => ‖T - integralBandProjection T + hk.truncatedOperator n‖
  let c : ℝ := sInf (Set.range q)
  let s : X → ℝ := fun x => (kernelSingularPart κ ν x).real univ
  let d : X → ℝ := fun x => c - s x
  have hc : 0 ≤ c := le_csInf (Set.range_nonempty _) (by
    rintro _ ⟨n, rfl⟩
    exact norm_nonneg _)
  have hsmeas : Measurable s :=
    (Kernel.measurable_coe (kernelSingularPart κ ν) MeasurableSet.univ).ennreal_toReal
  have hdmeas : Measurable d := measurable_const.sub hsmeas
  have hsle : ∀ᵐ x ∂μ, s x ≤ c := by
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, s x ≤ q n := by
      apply eventually_countable_forall.mpr
      intro n
      filter_upwards [positive_kernel_remainder_mass_bound T hT κ hrepr hk n] with x hx
      have hnonneg : 0 ≤ ∫ y, ‖truncatedKernel n (kernelRealDensity κ ν) (x, y)‖ ∂ν :=
        integral_nonneg (fun y => norm_nonneg _)
      dsimp only [s, q]
      linarith
    filter_upwards [hall] with x hx
    exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨n, rfl⟩; exact hx n)
  have hd0 : ∀ᵐ x ∂μ, 0 ≤ d x := hsle.mono fun x hx => sub_nonneg.mpr hx
  let H := hk.budgetClippedOperator hdmeas
  have hweak : IsWeaklyCompactOperator H := by
    apply hk.weaklyCompact_budgetClippedOperator hdmeas hd0
    intro ε hε
    obtain ⟨r, ⟨n, rfl⟩, hn⟩ := exists_lt_of_csInf_lt (Set.range_nonempty q)
      (show sInf (Set.range q) < c + ε from lt_add_of_pos_right c hε)
    refine ⟨n, ?_⟩
    filter_upwards [positive_kernel_remainder_mass_bound T hT κ hrepr hk n,
      hk.clipResidualMass_le_truncatedKernel n] with x hx hRx
    apply max_le _ hε.le
    dsimp only [d, s]
    change ‖T - integralBandProjection T + hk.truncatedOperator n‖ < c + ε at hn
    linarith
  have hH : 0 ≤ H := (hk.isIntegralKernel_budgetClippedOperator hdmeas).positive_of_nonneg_ae
    (Eventually.of_forall fun z => budgetClipKernel_nonneg (kernelRealDensity_nonneg κ ν) d z)
  have hHP : H ≤ integralBandProjection T := sub_nonneg.mp
    ((hk.sub (hk.isIntegralKernel_budgetClippedOperator hdmeas)).positive_of_nonneg_ae
      (Eventually.of_forall fun z => sub_nonneg.mpr
        (budgetClipKernel_le_self (kernelRealDensity_nonneg κ ν) d z)))
  refine ⟨H, hweak, hH, hHP, ?_⟩
  apply positive_budgetClippedOperator_error_norm_le κ ν T hT hrepr hk hdmeas hc hd0
  exact Eventually.of_forall fun x => by
    have hm := min_le_right (∫ y, ‖kernelRealDensity κ ν (x, y)‖ ∂ν) (d x)
    dsimp only [d, s] at hm
    linarith

end ThesisCommon
