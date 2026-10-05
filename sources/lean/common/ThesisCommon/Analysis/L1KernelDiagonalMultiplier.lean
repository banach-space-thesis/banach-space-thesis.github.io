import ThesisCommon.Analysis.L1OperatorMeasureRestrictions
import ThesisCommon.Analysis.SignedKernelDiagonalTrace
import ThesisCommon.Analysis.LpBoundedMultiplier

/-! The diagonal restriction of an actual positive L1 operator measure is
exactly multiplication by the measurable diagonal mass of its reverse kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

def kernelDiagonalFunction (κ : Kernel X X) (x : X) : ℝ := (κ x).real {x}

theorem kernelDiagonalFunction_measurable (κ : Kernel X X) [IsFiniteKernel κ] :
    Measurable (kernelDiagonalFunction κ) := (measurable_kernel_diagonal κ).ennreal_toReal

theorem kernelDiagonalFunction_bound (κ : Kernel X X) [IsFiniteKernel κ]
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, κ x univ ≤ ENNReal.ofReal C) (x : X) :
    ‖kernelDiagonalFunction κ x‖ ≤ C := by
  rw [kernelDiagonalFunction, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact (measureReal_mono (subset_univ _)).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb x)).trans_eq (ENNReal.toReal_ofReal hC))

theorem kernel_diagonal_restriction_eval (κ : Kernel X X) [IsFiniteKernel κ]
    (b : Set X) (hb : MeasurableSet b) (x : X) :
    (productSetKernel κ (diagonal X) x).real b = b.indicator (kernelDiagonalFunction κ) x := by
  rw [productSetKernel_apply κ _ isClosed_diagonal.measurableSet]
  have hs : Prod.mk x ⁻¹' diagonal X = {x} := by ext y; simp [eq_comm]
  rw [hs, measureReal_def, Measure.restrict_apply hb]
  by_cases hx : x ∈ b
  · rw [inter_eq_right.mpr (singleton_subset_iff.mpr hx), indicator_of_mem hx]
    rfl
  · have he : b ∩ {x} = ∅ := by ext y; simp; aesop
    rw [he, measure_empty, ENNReal.toReal_zero, indicator_of_notMem hx]

variable {μ : Measure X} [IsFiniteMeasure μ]

def kernelDiagonalMultiplier (κ : Kernel X X) [IsFiniteKernel κ]
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, κ x univ ≤ ENNReal.ofReal C) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ :=
  lpBoundedMultiplier (kernelDiagonalFunction κ)
    (kernelDiagonalFunction_measurable κ).aestronglyMeasurable C
    (Eventually.of_forall (kernelDiagonalFunction_bound κ C hC hb))

theorem kernelDiagonalMultiplier_coe (κ : Kernel X X) [IsFiniteKernel κ]
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, κ x univ ≤ ENNReal.ofReal C) (f : Lp ℝ 1 μ) :
    kernelDiagonalMultiplier κ C hC hb f =ᵐ[μ] fun x => kernelDiagonalFunction κ x * f x :=
  lpBoundedMultiplier_coe _ _ _ _ f

theorem kernelDiagonalMultiplier_nonneg (κ : Kernel X X) [IsFiniteKernel κ]
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, κ x univ ≤ ENNReal.ofReal C) :
    0 ≤ kernelDiagonalMultiplier (μ := μ) κ C hC hb := by
  intro f hf
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [kernelDiagonalMultiplier_coe κ C hC hb f, (Lp.coeFn_nonneg _).mpr hf] with x hx hn
  rw [hx]
  exact mul_nonneg measureReal_nonneg hn

variable [CompactSpace X] [TotallyDisconnectedSpace X]

theorem lOnePositiveRelation_diagonal_eq_multiplier
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (hS : 0 ≤ S)
    (κ : Kernel X X) [IsFiniteKernel κ] (hκ : μ ⊗ₘ κ = clopenOperatorMeasure S hS)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, κ x univ ≤ ENNReal.ofReal C) :
    lOnePositiveRelation S hS (diagonal X) = kernelDiagonalMultiplier κ C hC hb := by
  apply clopenOperatorMeasure_injective _ _ (lOnePositiveRelation_nonneg S hS _)
    (kernelDiagonalMultiplier_nonneg κ C hC hb)
  rw [(lOnePositiveRelation_spec S hS _).2, ← hκ,
    ← compProd_productSetKernel μ κ _ isClosed_diagonal.measurableSet]
  apply Measure.ext_prod
  intro a b ha hbb
  rw [clopenOperatorMeasure_prod _ _ ha hbb]
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  change (μ ⊗ₘ productSetKernel κ (diagonal X)).real (a ×ˢ b) = _
  rw [← setIntegral_kernel_real_eval μ (productSetKernel κ (diagonal X)) a ha b hbb]
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae
    (ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr
      (kernelDiagonalMultiplier_nonneg κ C hC hb _ (lOneIndicator_nonneg a ha)))))]
  simp_rw [kernel_diagonal_restriction_eval κ b hbb]
  rw [setIntegral_indicator hbb]
  have he : (fun x => kernelDiagonalMultiplier κ C hC hb (lOneIndicator μ a ha) x) =ᵐ[μ]
      a.indicator (kernelDiagonalFunction κ) := by
    filter_upwards [kernelDiagonalMultiplier_coe κ C hC hb (lOneIndicator μ a ha),
      lOneIndicator_coe (μ := μ) a ha] with x hx hi
    rw [hx, hi]
    by_cases hxa : x ∈ a <;> simp [hxa]
  rw [integral_congr_ae (ae_restrict_of_ae he), setIntegral_indicator ha, inter_comm]

end ThesisCommon
