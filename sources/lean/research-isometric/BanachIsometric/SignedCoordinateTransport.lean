import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Signed Jacobian integrals under actual auxiliary coordinates

Coordinate space has its original norm. In particular this bridge does not
install a Euclidean norm on `Fin n → ℝ`. Conjugation preserves the determinant
of the actual derivative, including at nondifferentiability points. Transport
of the measure then preserves the complete signed weighted integral.
-/

namespace BanachIsometric

open MeasureTheory Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def coordinateMapConjugate (e : E ≃L[ℝ] F) (f : E → E) (y : F) : F := e (f (e.symm y))

theorem fderiv_coordinateConjugate (e : E ≃L[ℝ] F) (f : E → E) (x : E) :
    fderiv ℝ (coordinateMapConjugate e f) (e x) =
      (e : E →L[ℝ] F).comp ((fderiv ℝ f x).comp (e.symm : F →L[ℝ] E)) := by
  change fderiv ℝ (e ∘ (f ∘ e.symm)) (e x) = _
  rw [e.comp_fderiv, e.symm.comp_right_fderiv, e.symm_apply_apply]

theorem det_fderiv_coordinateConjugate (e : E ≃L[ℝ] F) (f : E → E) (x : E) :
    (fderiv ℝ (coordinateMapConjugate e f) (e x)).det = (fderiv ℝ f x).det := by
  rw [fderiv_coordinateConjugate]
  exact LinearMap.det_conj (fderiv ℝ f x).toLinearMap e.toLinearEquiv

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The whole signed integral, with the actual transported measure. No
absolute determinant replaces the signed derivative determinant. -/
theorem integral_signedJacobian_coordinateConjugate (μ : Measure E)
    (e : E ≃L[ℝ] F) (f : E → E) (S : Set E) (g : E → ℝ) :
    (∫ y in e '' S, (fderiv ℝ (coordinateMapConjugate e f) y).det *
      g (e.symm (coordinateMapConjugate e f y)) ∂Measure.map e μ) =
      ∫ x in S, (fderiv ℝ f x).det * g (f x) ∂μ := by
  have hm := setIntegral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv
    (fun y => (fderiv ℝ (coordinateMapConjugate e f) y).det *
      g (e.symm (coordinateMapConjugate e f y))) (e '' S)
  change (∫ y in e '' S, (fderiv ℝ (coordinateMapConjugate e f) y).det *
    g (e.symm (coordinateMapConjugate e f y)) ∂Measure.map e μ) = _ at hm
  rw [hm]
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    Set.preimage_image_eq _ e.injective, det_fderiv_coordinateConjugate,
    coordinateMapConjugate, e.symm_apply_apply]

end BanachIsometric
