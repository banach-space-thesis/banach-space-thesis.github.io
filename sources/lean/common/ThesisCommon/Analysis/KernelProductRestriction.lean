import ThesisCommon.Analysis.BoundedKernelDisintegration
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-! Restriction of a measurable kernel along a measurable set in the product,
and the pointwise Jordan decomposition obtained by splitting each fibre
along that set and its complement. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem measurable_productSetIndicator (s : Set (X × Y)) (hs : MeasurableSet s) :
    Measurable (Function.uncurry (fun x y => s.indicator (fun _ => (1 : ℝ≥0∞)) (x, y))) :=
  measurable_const.indicator hs

def productSetKernel (κ : Kernel X Y) [IsFiniteKernel κ] (s : Set (X × Y)) : Kernel X Y :=
  κ.withDensity (fun x y => s.indicator (fun _ => 1) (x, y))

instance productSetKernel_finite (κ : Kernel X Y) [IsFiniteKernel κ] (s : Set (X × Y)) :
    IsFiniteKernel (productSetKernel κ s) := by
  apply Kernel.isFiniteKernel_withDensity_of_bounded κ (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
  intro x y
  exact indicator_le_self' (fun _ _ => zero_le _) (x, y)

theorem productSetKernel_apply (κ : Kernel X Y) [IsFiniteKernel κ]
    (s : Set (X × Y)) (hs : MeasurableSet s) (x : X) :
    productSetKernel κ s x = (κ x).restrict (Prod.mk x ⁻¹' s) := by
  rw [productSetKernel, Kernel.withDensity_apply _ (measurable_productSetIndicator s hs)]
  exact withDensity_indicator_one (measurable_prodMk_left hs)

theorem productSetKernel_add_compl (κ : Kernel X Y) [IsFiniteKernel κ]
    (s : Set (X × Y)) (hs : MeasurableSet s) (x : X) :
    productSetKernel κ s x + productSetKernel κ sᶜ x = κ x := by
  rw [productSetKernel_apply κ s hs, productSetKernel_apply κ sᶜ hs.compl, preimage_compl,
    Measure.restrict_add_restrict_compl (measurable_prodMk_left hs)]

theorem productSetKernel_mutuallySingular (κ : Kernel X Y) [IsFiniteKernel κ]
    (s : Set (X × Y)) (hs : MeasurableSet s) (x : X) :
    productSetKernel κ s x ⟂ₘ productSetKernel κ sᶜ x := by
  rw [productSetKernel_apply κ s hs, productSetKernel_apply κ sᶜ hs.compl, preimage_compl]
  refine ⟨(Prod.mk x ⁻¹' s)ᶜ, (measurable_prodMk_left hs).compl, ?_, ?_⟩
  · rw [Measure.restrict_apply (measurable_prodMk_left hs).compl, compl_inter_self, measure_empty]
  · rw [compl_compl, Measure.restrict_apply (measurable_prodMk_left hs), inter_compl_self, measure_empty]

theorem compProd_productSetKernel (μ : Measure X) [SFinite μ]
    (κ : Kernel X Y) [IsFiniteKernel κ] (s : Set (X × Y)) (hs : MeasurableSet s) :
    μ ⊗ₘ productSetKernel κ s = (μ ⊗ₘ κ).restrict s := by
  letI : IsFiniteKernel (κ.withDensity (fun x y => s.indicator (fun _ => (1 : ℝ≥0∞)) (x, y))) :=
    productSetKernel_finite κ s
  rw [productSetKernel, Measure.compProd_withDensity (κ := κ) (measurable_productSetIndicator s hs)]
  exact withDensity_indicator_one hs

def kernelSplitJordan (κ : Kernel X Y) [IsFiniteKernel κ]
    (s : Set (X × Y)) (hs : MeasurableSet s) (x : X) : JordanDecomposition Y where
  posPart := productSetKernel κ s x
  negPart := productSetKernel κ sᶜ x
  mutuallySingular := productSetKernel_mutuallySingular κ s hs x

def kernelSplitSigned (κ : Kernel X Y) [IsFiniteKernel κ]
    (s : Set (X × Y)) (hs : MeasurableSet s) (x : X) : SignedMeasure Y :=
  (kernelSplitJordan κ s hs x).toSignedMeasure

theorem kernelSplitSigned_totalVariation (κ : Kernel X Y) [IsFiniteKernel κ]
    (s : Set (X × Y)) (hs : MeasurableSet s) (x : X) :
    (kernelSplitSigned κ s hs x).totalVariation = κ x := by
  rw [kernelSplitSigned, SignedMeasure.totalVariation,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  exact productSetKernel_add_compl κ s hs x

theorem kernelSplitSigned_measurable (κ : Kernel X Y) [IsFiniteKernel κ]
    (s : Set (X × Y)) (hs : MeasurableSet s) (b : Set Y) (hb : MeasurableSet b) :
    Measurable (fun x => kernelSplitSigned κ s hs x b) := by
  have hrepr : (fun x => kernelSplitSigned κ s hs x b) =
      (fun x => (productSetKernel κ s x b).toReal - (productSetKernel κ sᶜ x b).toReal) := by
    funext x
    exact Measure.toSignedMeasure_sub_apply hb
  rw [hrepr]
  exact (Kernel.measurable_coe _ hb).ennreal_toReal.sub (Kernel.measurable_coe _ hb).ennreal_toReal

end ThesisCommon
