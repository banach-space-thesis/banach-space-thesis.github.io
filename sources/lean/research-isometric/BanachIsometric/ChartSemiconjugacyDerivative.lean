import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Actual derivatives obtained from local chart identities

An invertible strict source-chart derivative gives a genuine local inverse.
An actual local semiconjugacy identity then determines the derivative of the
represented map. In particular two negatively oriented charts around a
positive affine strip yield a positive actual derivative determinant.
-/

namespace BanachIsometric

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem hasFDerivAt_of_chart_semiconjugacy
    {S T L f : E → E} {A : E ≃L[ℝ] E} {B D : E →L[ℝ] E} {x : E}
    (hS : HasStrictFDerivAt S (A : E →L[ℝ] E) x)
    (hT : HasFDerivAt T B (L x)) (hL : HasFDerivAt L D x)
    (heq : ∀ᶠ z in 𝓝 x, f (S z) = T (L z)) :
    HasFDerivAt f ((B.comp D).comp (A.symm : E →L[ℝ] E)) (S x) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have houter := hT.comp x hL
  have houter' : HasFDerivAt (fun z => T (L z)) (B.comp D)
      (hS.localInverse S A x (S x)) := by
    rw [hS.localInverse_apply_image]
    exact houter
  have hc := houter'.comp (S x) hS.to_localInverse.hasFDerivAt
  have hpull := hS.localInverse_tendsto.eventually heq
  have heq' : (fun z => T (L (hS.localInverse S A x z))) =ᶠ[𝓝 (S x)] f := by
    filter_upwards [hpull, hS.eventually_right_inverse] with z hz hzinv
    rw [hzinv] at hz
    exact hz.symm
  exact hc.congr_of_eventuallyEq heq'.symm

theorem det_fderiv_eq_of_chart_semiconjugacy
    {S T L f : E → E} {A : E ≃L[ℝ] E} {B D : E →L[ℝ] E} {x : E}
    (hS : HasStrictFDerivAt S (A : E →L[ℝ] E) x)
    (hT : HasFDerivAt T B (L x)) (hL : HasFDerivAt L D x)
    (heq : ∀ᶠ z in 𝓝 x, f (S z) = T (L z)) :
    (fderiv ℝ f (S x)).det = B.det * D.det * (A : E →L[ℝ] E).det⁻¹ := by
  rw [(hasFDerivAt_of_chart_semiconjugacy hS hT hL heq).fderiv]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    ContinuousLinearEquiv.det_coe_symm]

theorem det_fderiv_pos_of_negative_chart_semiconjugacy
    {S T L f : E → E} {A : E ≃L[ℝ] E} {B D : E →L[ℝ] E} {x : E}
    (hS : HasStrictFDerivAt S (A : E →L[ℝ] E) x)
    (hT : HasFDerivAt T B (L x)) (hL : HasFDerivAt L D x)
    (heq : ∀ᶠ z in 𝓝 x, f (S z) = T (L z))
    (hA : (A : E →L[ℝ] E).det < 0) (hB : B.det < 0) (hD : 0 < D.det) :
    0 < (fderiv ℝ f (S x)).det := by
  rw [det_fderiv_eq_of_chart_semiconjugacy hS hT hL heq]
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hB hD) (inv_lt_zero.mpr hA)

end BanachIsometric
