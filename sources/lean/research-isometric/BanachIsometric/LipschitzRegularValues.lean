import BanachIsometric.SignedArea
import BanachIsometric.LipschitzNullImages
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Almost every value of a Lipschitz map has only regular preimages

The image of the nondifferentiability set is null by Rademacher and Lusin (N).
The image of the differentiable singular set is null by the Jacobian library's
equal-dimension Sard lemma. Thus almost every entire fiber consists of actual
differentiability points with nonzero determinant, without C¹ regularity.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The image of the actual differentiable singular points is null for an
arbitrary map. This statement does not assume global differentiability. -/
theorem measure_image_differentiable_singular_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) :
    μ (f '' {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (f' := fderiv ℝ f) μ
  · intro x hx
    exact hx.1.hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact hx.2

/-- The exceptional values hit by any nonregular source point form a null set
for a Lipschitz map in equal finite real dimensions. -/
theorem lipschitzWith_image_nonregular_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) :
    μ (f '' (differentiableRegularSet f)ᶜ) = 0 := by
  have hN : μ {x | ¬DifferentiableAt ℝ f x} = 0 :=
    ae_iff.mp (hf.ae_differentiableAt (μ := μ))
  have hNI : μ (f '' {x | ¬DifferentiableAt ℝ f x}) = 0 :=
    lipschitzWith_sends_null_sets_to_null μ μ rfl hf _ hN
  have hset : (differentiableRegularSet f)ᶜ =
      {x | ¬DifferentiableAt ℝ f x} ∪
        {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det = 0} := by
    classical
    ext x
    by_cases hx : DifferentiableAt ℝ f x <;> simp [differentiableRegularSet, hx]
  rw [hset, Set.image_union]
  exact measure_union_null hNI (measure_image_differentiable_singular_eq_zero μ f)

/-- Almost every target value has no nondifferentiable or singular preimage.
Finiteness of the fiber on a compact source can be supplied independently by
isolation at an invertible derivative. -/
theorem lipschitzWith_ae_every_preimage_regular (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ y ∂μ, ∀ x, f x = y →
      DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det ≠ 0 := by
  have hbad := lipschitzWith_image_nonregular_eq_zero μ hf
  have hae : ∀ᵐ y ∂μ, y ∉ f '' (differentiableRegularSet f)ᶜ := by
    rw [ae_iff]
    simpa only [not_not] using hbad
  filter_upwards [hae] with y hy
  intro x hxy
  by_contra hx
  exact hy ⟨x, hx, hxy⟩

end BanachIsometric
