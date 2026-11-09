import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Data.Sign.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Signed change of variables on actual injective branches

The Jacobian library supplies the absolute-determinant formula. Weighting the
target by the orientation sign at its unique inverse gives a signed formula.
The inverse and its sign are explicitly defined from the map, not supplied as
degree data. Later countable branches will be constructed from differentiability
and invertible derivatives.
-/

namespace BanachIsometric

open MeasureTheory Set Function
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The real orientation sign of a specified derivative field. -/
noncomputable def jacobianOrientation (D : E → E →L[ℝ] E) (x : E) : ℝ :=
  SignType.sign (D x).det

/-- A branch's signed target weight, extended by zero outside its image.
On an injective branch the inverse is forced, independently of the choice in
`invFunOn`. -/
noncomputable def signedBranchWeight (f : E → E) (D : E → E →L[ℝ] E)
    (s : Set E) (g : E → ℝ) : E → ℝ :=
  (f '' s).indicator (fun y => jacobianOrientation D (invFunOn f s y) * g y)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem signedBranchWeight_apply_image {f : E → E} {D : E → E →L[ℝ] E}
    {s : Set E} (hf : InjOn f s) (g : E → ℝ) {x : E} (hx : x ∈ s) :
    signedBranchWeight f D s g (f x) = jacobianOrientation D x * g (f x) := by
  unfold signedBranchWeight
  rw [indicator_of_mem (mem_image_of_mem f hx), hf.leftInvOn_invFunOn hx]

/-- Signed injective change of variables. The sign on the target is evaluated
at the actual unique inverse of the map. No constancy or degree hypothesis is
present, and the source need only carry derivatives within the measurable set.
-/
theorem integral_signedBranchWeight (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {D : E → E →L[ℝ] E} {s : Set E} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hf : InjOn f s) (g : E → ℝ) :
    (∫ y, signedBranchWeight f D s g y ∂μ) =
      ∫ x in s, (D x).det * g (f x) ∂μ := by
  have himg : MeasurableSet (f '' s) := measurable_image_of_fderivWithin hs hD hf
  rw [signedBranchWeight, integral_indicator himg,
    integral_image_eq_integral_abs_det_fderiv_smul μ hs hD hf]
  apply setIntegral_congr_fun hs
  intro x hx
  change |(D x).det| • (jacobianOrientation D (invFunOn f s (f x)) * g (f x)) =
    (D x).det * g (f x)
  rw [hf.leftInvOn_invFunOn hx]
  simp only [jacobianOrientation, smul_eq_mul, ← mul_assoc, abs_mul_sign]

/-- Integrability is transported with the same signed source integrand.
This will provide, rather than assume, integrability of the branch sum. -/
theorem integrable_signedBranchWeight_iff (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {D : E → E →L[ℝ] E} {s : Set E} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hf : InjOn f s) (g : E → ℝ) :
    Integrable (signedBranchWeight f D s g) μ ↔
      IntegrableOn (fun x => (D x).det * g (f x)) s μ := by
  have himg : MeasurableSet (f '' s) := measurable_image_of_fderivWithin hs hD hf
  rw [signedBranchWeight, integrable_indicator_iff himg,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hD hf]
  apply integrableOn_congr_fun _ hs
  intro x hx
  change |(D x).det| • (jacobianOrientation D (invFunOn f s (f x)) * g (f x)) =
    (D x).det * g (f x)
  rw [hf.leftInvOn_invFunOn hx]
  simp only [jacobianOrientation, smul_eq_mul, ← mul_assoc, abs_mul_sign]

/-- Absolute integrals of the signed branch weight are exactly absolute
integrals of the signed source Jacobian. This gives the summability needed
for the countably many injective branches. -/
theorem integral_norm_signedBranchWeight (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {D : E → E →L[ℝ] E} {s : Set E} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hf : InjOn f s) (g : E → ℝ) :
    (∫ y, ‖signedBranchWeight f D s g y‖ ∂μ) =
      ∫ x in s, ‖(D x).det * g (f x)‖ ∂μ := by
  have himg : MeasurableSet (f '' s) := measurable_image_of_fderivWithin hs hD hf
  simp only [signedBranchWeight, norm_indicator_eq_indicator_norm]
  rw [integral_indicator himg,
    integral_image_eq_integral_abs_det_fderiv_smul μ hs hD hf]
  apply setIntegral_congr_fun hs
  intro x hx
  change |(D x).det| • ‖jacobianOrientation D (invFunOn f s (f x)) * g (f x)‖ =
    ‖(D x).det * g (f x)‖
  rw [hf.leftInvOn_invFunOn hx]
  have hsign (a : ℝ) : |a| * |(SignType.sign a : ℝ)| = |a| := by
    simpa only [abs_mul, abs_abs] using congrArg abs (abs_mul_sign a)
  simp only [jacobianOrientation, smul_eq_mul, Real.norm_eq_abs, abs_mul,
    ← mul_assoc, hsign]

end BanachIsometric
