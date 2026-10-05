import ThesisCommon.Analysis.IntegralKernel
import Mathlib.Probability.Kernel.CompProdEqIff

/-! Jointly measurable Lebesgue decomposition of a finite kernel.

The density comes from `Kernel.rnDeriv`, not from separately choosing a
Radon--Nikodym derivative in each fibre. Its real conversion is justified
almost everywhere in every fibre. The singular part remains a genuine
measurable finite kernel. The product decomposition and product singularity
then identify these terms with the usual Lebesgue parts of the product.

The measurable-space assumption is mathlib's countable-or-countably-generated
condition; a countably generated (in particular standard Borel) target is
sufficient. No nonempty-space or nonzero-measure hypothesis is used.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [MeasurableSpace.CountableOrCountablyGenerated X Y]

/-- The jointly measurable real density of a kernel relative to a fixed
measure. Infinite values of the extended density are sent to zero; the
finite-kernel results below prove this changes no fibre density measure. -/
def kernelRealDensity (κ : Kernel X Y) (ν : Measure Y) (z : X × Y) : ℝ :=
  (κ.rnDeriv (Kernel.const X ν) z.1 z.2).toReal

theorem measurable_kernelRealDensity (κ : Kernel X Y) (ν : Measure Y) :
    Measurable (kernelRealDensity κ ν) :=
  (Kernel.measurable_rnDeriv κ (Kernel.const X ν)).ennreal_toReal

theorem kernelRealDensity_nonneg (κ : Kernel X Y) (ν : Measure Y) (z : X × Y) :
    0 ≤ kernelRealDensity κ ν z := ENNReal.toReal_nonneg

variable (κ : Kernel X Y) [IsFiniteKernel κ] (ν : Measure Y) [IsFiniteMeasure ν]

theorem ofReal_kernelRealDensity_ae (x : X) :
    (fun y => ENNReal.ofReal (kernelRealDensity κ ν (x, y))) =ᵐ[ν]
      κ.rnDeriv (Kernel.const X ν) x := by
  have h := Kernel.rnDeriv_ne_top κ (Kernel.const X ν) (a := x)
  filter_upwards [h] with y hy
  exact ENNReal.ofReal_toReal hy

/-- The absolutely continuous kernel defined using the actual real density. -/
def kernelAbsolutelyContinuousPart : Kernel X Y :=
  (Kernel.const X ν).withDensity (fun x y => ENNReal.ofReal (kernelRealDensity κ ν (x, y)))

/-- The genuine jointly measurable singular kernel. -/
def kernelSingularPart : Kernel X Y := κ.singularPart (Kernel.const X ν)

omit [IsFiniteKernel κ] in
theorem kernelAbsolutelyContinuousPart_apply (x : X) :
    kernelAbsolutelyContinuousPart κ ν x =
      ν.withDensity (fun y => ENNReal.ofReal (kernelRealDensity κ ν (x, y))) := by
  rw [kernelAbsolutelyContinuousPart, Kernel.withDensity_apply _
    (measurable_kernelRealDensity κ ν).ennreal_ofReal, Kernel.const_apply]

theorem kernelAbsolutelyContinuousPart_eq_rnDeriv :
    kernelAbsolutelyContinuousPart κ ν =
      (Kernel.const X ν).withDensity (κ.rnDeriv (Kernel.const X ν)) :=
  Kernel.withDensity_congr_ae (Kernel.const X ν)
    (measurable_kernelRealDensity κ ν).ennreal_ofReal
    (Kernel.measurable_rnDeriv κ (Kernel.const X ν)) (ofReal_kernelRealDensity_ae κ ν)

instance kernelAbsolutelyContinuousPart_isFinite :
    IsFiniteKernel (kernelAbsolutelyContinuousPart κ ν) := by
  rw [kernelAbsolutelyContinuousPart_eq_rnDeriv]
  infer_instance

instance kernelSingularPart_isFinite : IsFiniteKernel (kernelSingularPart κ ν) := by
  unfold kernelSingularPart
  infer_instance

theorem kernelAbsolutelyContinuousPart_add_singularPart :
    kernelAbsolutelyContinuousPart κ ν + kernelSingularPart κ ν = κ := by
  rw [kernelAbsolutelyContinuousPart_eq_rnDeriv, kernelSingularPart]
  exact Kernel.rnDeriv_add_singularPart κ (Kernel.const X ν)

theorem kernel_lebesgue_decomposition (x : X) :
    κ x = ν.withDensity (fun y => ENNReal.ofReal (kernelRealDensity κ ν (x, y))) +
      kernelSingularPart κ ν x := by
  have h := congrArg (fun η : Kernel X Y => η x)
    (kernelAbsolutelyContinuousPart_add_singularPart κ ν)
  simpa only [Kernel.add_apply, kernelAbsolutelyContinuousPart_apply] using h.symm

theorem kernelSingularPart_mutuallySingular (x : X) : kernelSingularPart κ ν x ⟂ₘ ν :=
  Kernel.mutuallySingular_singularPart κ (Kernel.const X ν) x

theorem lintegral_kernel_rnDeriv_le (x : X) :
    (∫⁻ y, κ.rnDeriv (Kernel.const X ν) x y ∂ν) ≤ κ x univ := by
  simpa only [setLIntegral_univ, Kernel.const_apply] using
    (Kernel.setLIntegral_rnDeriv_le (κ := κ) (η := Kernel.const X ν) (a := x) MeasurableSet.univ)

theorem integrable_kernelRealDensity_column (x : X) :
    Integrable (fun y => kernelRealDensity κ ν (x, y)) ν :=
  integrable_toReal_of_lintegral_ne_top
    (Kernel.measurable_rnDeriv_right κ (Kernel.const X ν) x).aemeasurable
    ((lintegral_kernel_rnDeriv_le κ ν x).trans_lt (measure_lt_top (κ x) univ)).ne

theorem integral_kernelRealDensity_column_le (x : X) :
    (∫ y, kernelRealDensity κ ν (x, y) ∂ν) ≤ (κ x univ).toReal := by
  change (∫ y, (κ.rnDeriv (Kernel.const X ν) x y).toReal ∂ν) ≤ _
  have htop : ∀ᵐ y ∂ν, κ.rnDeriv (Kernel.const X ν) x y < ∞ := by
    simpa only [Kernel.const_apply] using (Kernel.rnDeriv_lt_top κ (Kernel.const X ν) (a := x))
  rw [integral_toReal (μ := ν)
    (Kernel.measurable_rnDeriv_right κ (Kernel.const X ν) x).aemeasurable htop]
  exact ENNReal.toReal_mono (measure_ne_top (κ x) univ) (lintegral_kernel_rnDeriv_le κ ν x)

/-- Uniform fibre mass gives the precise column bound required by the
integral-operator constructor, for any base measure on the source space. -/
theorem kernelRealDensity_hasKernelBound (μ : Measure X) {C : ℝ} (hC : 0 ≤ C)
    (hκC : ∀ x, κ x univ ≤ ENNReal.ofReal C) : HasKernelBound μ ν (kernelRealDensity κ ν) C := by
  apply Eventually.of_forall
  intro x
  refine ⟨integrable_kernelRealDensity_column κ ν x, ?_⟩
  calc
    (∫ y, ‖kernelRealDensity κ ν (x, y)‖ ∂ν) =
        ∫ y, kernelRealDensity κ ν (x, y) ∂ν := by
      simp only [Real.norm_eq_abs, abs_of_nonneg (kernelRealDensity_nonneg κ ν _)]
    _ ≤ (κ x univ).toReal := integral_kernelRealDensity_column_le κ ν x
    _ ≤ C := ENNReal.toReal_le_of_le_ofReal hC (hκC x)

variable (μ : Measure X) [SFinite μ]

theorem compProd_kernelAbsolutelyContinuousPart :
    μ ⊗ₘ kernelAbsolutelyContinuousPart κ ν =
      (μ.prod ν).withDensity (fun z => ENNReal.ofReal (kernelRealDensity κ ν z)) := by
  letI : IsFiniteKernel ((Kernel.const X ν).withDensity
      (fun x y => ENNReal.ofReal (kernelRealDensity κ ν (x, y)))) :=
    kernelAbsolutelyContinuousPart_isFinite κ ν
  change μ ⊗ₘ (Kernel.const X ν).withDensity
      (fun x y => ENNReal.ofReal (kernelRealDensity κ ν (x, y))) = _
  rw [Measure.compProd_withDensity (measurable_kernelRealDensity κ ν).ennreal_ofReal,
    Measure.compProd_const]

theorem compProd_kernel_lebesgue_decomposition :
    μ ⊗ₘ κ = (μ.prod ν).withDensity (fun z => ENNReal.ofReal (kernelRealDensity κ ν z)) +
      μ ⊗ₘ kernelSingularPart κ ν := by
  calc
    μ ⊗ₘ κ = μ ⊗ₘ (kernelAbsolutelyContinuousPart κ ν + kernelSingularPart κ ν) := by
      rw [kernelAbsolutelyContinuousPart_add_singularPart]
    _ = μ ⊗ₘ kernelAbsolutelyContinuousPart κ ν + μ ⊗ₘ kernelSingularPart κ ν :=
      Measure.compProd_add_right _ _ _
    _ = _ := by rw [compProd_kernelAbsolutelyContinuousPart]

theorem compProd_kernelSingularPart_mutuallySingular :
    μ ⊗ₘ kernelSingularPart κ ν ⟂ₘ μ.prod ν := by
  have h := Measure.MutuallySingular.compProd_of_right μ μ
    (κ := kernelSingularPart κ ν) (η := Kernel.const X ν)
    (Eventually.of_forall (kernelSingularPart_mutuallySingular κ ν))
  simpa only [Measure.compProd_const] using h

/-- Identification with the ordinary product-measure absolutely continuous
part, by uniqueness of Lebesgue decomposition. -/
theorem kernelRealDensity_withDensity_eq_product_rnDeriv :
    (μ.prod ν).withDensity (fun z => ENNReal.ofReal (kernelRealDensity κ ν z)) =
      (μ.prod ν).withDensity ((μ ⊗ₘ κ).rnDeriv (μ.prod ν)) := by
  apply Measure.eq_withDensity_rnDeriv (measurable_kernelRealDensity κ ν).ennreal_ofReal
    (compProd_kernelSingularPart_mutuallySingular κ ν μ)
  rw [add_comm]
  exact compProd_kernel_lebesgue_decomposition κ ν μ

/-- The product of the measurable singular kernel is the actual singular
part of the product measure. -/
theorem compProd_kernelSingularPart_eq_product_singularPart :
    μ ⊗ₘ kernelSingularPart κ ν = (μ ⊗ₘ κ).singularPart (μ.prod ν) := by
  apply Measure.eq_singularPart (measurable_kernelRealDensity κ ν).ennreal_ofReal
    (compProd_kernelSingularPart_mutuallySingular κ ν μ)
  rw [add_comm]
  exact compProd_kernel_lebesgue_decomposition κ ν μ

omit [SFinite μ] in
/-- Direct bridge to constructions using the real Radon--Nikodym density
of the whole product measure. The equality is on the actual product base
measure, ready for integral-kernel transport by almost-everywhere equality. -/
theorem kernelRealDensity_eq_product_rnDeriv_toReal [SigmaFinite μ] :
    kernelRealDensity κ ν =ᵐ[μ.prod ν]
      fun z => ((μ ⊗ₘ κ).rnDeriv (μ.prod ν) z).toReal := by
  have hadd : μ ⊗ₘ κ = μ ⊗ₘ kernelSingularPart κ ν +
      (μ.prod ν).withDensity (fun z => ENNReal.ofReal (kernelRealDensity κ ν z)) := by
    rw [add_comm]
    exact compProd_kernel_lebesgue_decomposition κ ν μ
  have hden := Measure.eq_rnDeriv (measurable_kernelRealDensity κ ν).ennreal_ofReal
    (compProd_kernelSingularPart_mutuallySingular κ ν μ) hadd
  filter_upwards [hden] with z hz
  simpa only [ENNReal.toReal_ofReal (kernelRealDensity_nonneg κ ν z)] using
    congrArg ENNReal.toReal hz

end ThesisCommon
