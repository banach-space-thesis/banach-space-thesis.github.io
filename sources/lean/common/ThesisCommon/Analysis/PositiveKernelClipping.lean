import ThesisCommon.Analysis.IntegralKernelClipping
import ThesisCommon.Analysis.PositiveOperatorKernelParts
import ThesisCommon.Analysis.KernelOperatorNorm

/-! Positivity and the exact product measure of the clipping error. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
open scoped Classical

namespace ThesisCommon

theorem scalarClip_nonneg (t : ℝ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ scalarClip t a :=
  (le_min ha (le_max_right t 0)).trans (le_max_right _ _)

theorem scalarClip_le_self (t : ℝ) {a : ℝ} (ha : 0 ≤ a) : scalarClip t a ≤ a :=
  max_le ((neg_nonpos.mpr (le_max_right t 0)).trans ha) (min_le_left _ _)

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure Y}

omit [MeasurableSpace X] in
theorem budgetClip_nonneg {f : Y → ℝ} (hf : ∀ y, 0 ≤ f y) (d : ℝ) (y : Y) :
    0 ≤ budgetClip ν f d y := by
  unfold budgetClip
  split_ifs
  · exact scalarClip_nonneg _ (hf y)
  · exact hf y

omit [MeasurableSpace X] in
theorem budgetClip_le_self {f : Y → ℝ} (hf : ∀ y, 0 ≤ f y) (d : ℝ) (y : Y) :
    budgetClip ν f d y ≤ f y := by
  unfold budgetClip
  split_ifs
  · exact scalarClip_le_self _ (hf y)
  · exact le_rfl

omit [MeasurableSpace X] in
theorem budgetClipKernel_nonneg {k : X × Y → ℝ} (hk : ∀ z, 0 ≤ k z)
    (d : X → ℝ) (z : X × Y) : 0 ≤ budgetClipKernel ν k d z := by
  apply budgetClip_nonneg
  intro y
  dsimp only [integrableColumnKernel]
  split_ifs
  · exact hk _
  · exact le_rfl

omit [MeasurableSpace X] in
theorem budgetClipKernel_le_self {k : X × Y → ℝ} (hk : ∀ z, 0 ≤ k z)
    (d : X → ℝ) (z : X × Y) : budgetClipKernel ν k d z ≤ k z := by
  have hnonneg : ∀ y, 0 ≤ integrableColumnKernel ν k (z.1, y) := by
    intro y
    dsimp only [integrableColumnKernel]
    split_ifs
    · exact hk _
    · exact le_rfl
  apply (budgetClip_le_self hnonneg _ _).trans
  dsimp only [integrableColumnKernel]
  split_ifs
  · exact le_rfl
  · exact hk z

variable [MeasurableSpace.CountableOrCountablyGenerated X Y]
variable (κ : Kernel X Y) [IsFiniteKernel κ] (ν : Measure Y) [IsFiniteMeasure ν]

/-- Singular fibres together with the nonnegative density removed by budget clipping. -/
def kernelBudgetError (d : X → ℝ) : Kernel X Y :=
  kernelSingularPart κ ν + (Kernel.const X ν).withDensity (fun x y => ENNReal.ofReal
    (kernelRealDensity κ ν (x, y) - budgetClipKernel ν (kernelRealDensity κ ν) d (x, y)))

instance kernelBudgetError_sfinite (d : X → ℝ) : IsSFiniteKernel (kernelBudgetError κ ν d) := by
  letI : IsSFiniteKernel ((Kernel.const X ν).withDensity (fun x y => ENNReal.ofReal
    (kernelRealDensity κ ν (x, y) - budgetClipKernel ν (kernelRealDensity κ ν) d (x, y)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold kernelBudgetError
  infer_instance

theorem compProd_kernelBudgetError (μ : Measure X) [SFinite μ] {d : X → ℝ}
    (hd : Measurable d) : μ ⊗ₘ kernelBudgetError κ ν d = μ ⊗ₘ kernelSingularPart κ ν +
      (μ.prod ν).withDensity (fun z => ENNReal.ofReal
        (kernelRealDensity κ ν z - budgetClipKernel ν (kernelRealDensity κ ν) d z)) := by
  letI : IsSFiniteKernel ((Kernel.const X ν).withDensity (fun x y => ENNReal.ofReal
    (kernelRealDensity κ ν (x, y) - budgetClipKernel ν (kernelRealDensity κ ν) d (x, y)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  rw [kernelBudgetError, Measure.compProd_add_right, Measure.compProd_withDensity
    ((measurable_kernelRealDensity κ ν).sub
      (measurable_budgetClipKernel (measurable_kernelRealDensity κ ν) hd)).ennreal_ofReal,
    Measure.compProd_const]

theorem kernelBudgetError_apply_univ {d : X → ℝ} (hd : Measurable d) {x : X}
    (hd0 : 0 ≤ d x) : kernelBudgetError κ ν d x univ = kernelSingularPart κ ν x univ +
      ENNReal.ofReal (min (∫ y, ‖kernelRealDensity κ ν (x, y)‖ ∂ν) (d x)) := by
  let f : Y → ℝ := fun y => kernelRealDensity κ ν (x, y)
  have hf : Integrable f ν := integrable_kernelRealDensity_column κ ν x
  have heq := budgetClipKernel_column_eq (d := d) hf
  have hnonneg (y : Y) : 0 ≤ f y - budgetClip ν f (d x) y :=
    sub_nonneg.mpr (budgetClip_le_self (fun y => kernelRealDensity_nonneg κ ν (x, y)) _ _)
  have hi : Integrable (fun y => f y - budgetClip ν f (d x) y) ν :=
    hf.sub (integrable_budgetClip hf _)
  have hmass : (∫ y, f y - budgetClip ν f (d x) y ∂ν) = min (∫ y, ‖f y‖ ∂ν) (d x) := by
    rw [← integral_norm_sub_budgetClip hf hd0]
    exact integral_congr_ae (Eventually.of_forall fun y => (Real.norm_of_nonneg (hnonneg y)).symm)
  rw [kernelBudgetError, Kernel.add_apply, Measure.add_apply,
    Kernel.withDensity_apply _ ((measurable_kernelRealDensity κ ν).sub
      (measurable_budgetClipKernel (measurable_kernelRealDensity κ ν) hd)).ennreal_ofReal,
    Kernel.const_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  congr 1
  change (∫⁻ y, ENNReal.ofReal (f y - (fun y =>
    budgetClipKernel ν (kernelRealDensity κ ν) d (x, y)) y) ∂ν) = _
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hnonneg), hmass]

variable {μ : Measure X} [IsFiniteMeasure μ]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]

theorem positive_budgetClippedOperator_error_norm_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T)
    (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure T hT)
    (hk : IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection T))
    {d : X → ℝ} (hd : Measurable d) {C : ℝ} (hC : 0 ≤ C)
    (hd0 : ∀ᵐ x ∂μ, 0 ≤ d x)
    (hmass : ∀ᵐ x ∂μ, (kernelSingularPart κ ν x).real univ +
      min (∫ y, ‖kernelRealDensity κ ν (x, y)‖ ∂ν) (d x) ≤ C) :
    ‖T - hk.budgetClippedOperator hd‖ ≤ C := by
  have hR : 0 ≤ integralBandProjection T - hk.budgetClippedOperator hd :=
    (hk.sub (hk.isIntegralKernel_budgetClippedOperator hd)).positive_of_nonneg_ae
      (Eventually.of_forall fun z => sub_nonneg.mpr
        (budgetClipKernel_le_self (kernelRealDensity_nonneg κ ν) d z))
  have hS : 0 ≤ T - integralBandProjection T := sub_nonneg.mpr (integralBandProjection_le_id T hT)
  have hE : 0 ≤ T - hk.budgetClippedOperator hd := by
    have heq : T - hk.budgetClippedOperator hd =
        (T - integralBandProjection T) + (integralBandProjection T - hk.budgetClippedOperator hd) := by
      abel
    rw [heq]
    exact add_nonneg hS hR
  have hprod : μ ⊗ₘ kernelBudgetError κ ν d =
      clopenOperatorMeasure (T - hk.budgetClippedOperator hd) hE := by
    rw [compProd_kernelBudgetError κ ν μ hd,
      compProd_kernelSingularPart_eq_operator_residual T hT κ hrepr]
    have hadd : clopenOperatorMeasure (T - hk.budgetClippedOperator hd) hE =
        clopenOperatorMeasure (T - integralBandProjection T) hS +
        clopenOperatorMeasure (integralBandProjection T - hk.budgetClippedOperator hd) hR := by
      simpa only [sub_add_sub_cancel] using clopenOperatorMeasure_add
        (T - integralBandProjection T) (integralBandProjection T - hk.budgetClippedOperator hd) hS hR
    rw [hadd,
      (hk.sub (hk.isIntegralKernel_budgetClippedOperator hd)).clopenOperatorMeasure_eq hR]
    rfl
  apply (clopenOperatorMeasure_fst_le_iff_norm_le _ hE C hC).1
  rw [← hprod, compProd_fst_le_smul_iff]
  filter_upwards [hd0, hmass] with x hd0x hmx
  rw [kernelBudgetError_apply_univ κ ν hd hd0x]
  have hs0 : 0 ≤ (kernelSingularPart κ ν x).real univ := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ min (∫ y, ‖kernelRealDensity κ ν (x, y)‖ ∂ν) (d x) :=
    le_min (integral_nonneg fun y => norm_nonneg _) hd0x
  rw [show kernelSingularPart κ ν x univ = ENNReal.ofReal
      ((kernelSingularPart κ ν x).real univ) by
        exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,
    ← ENNReal.ofReal_add hs0 hm0]
  exact ENNReal.ofReal_le_ofReal hmx

end ThesisCommon
