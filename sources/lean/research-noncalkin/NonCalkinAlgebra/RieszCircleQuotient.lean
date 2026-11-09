import NonCalkinAlgebra.RieszCircleBasic
import NonCalkinAlgebra.EssentialIdempotentSpectrum
import SurveyStatements.P2InvariantQuotient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2 Metric
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (convention : QuotientConvention)

/-- Applying the quotient map to the actual Riesz integral gives 1-q(T).
Only the existence of the boundary resolvent is assumed here. -/
theorem essential_rieszCircle_image (T : BoundedOperators X)
    (hT : T * T - T ∈ operatorIdeal X convention) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ T) :
    operatorQuotientMap X convention (rieszCircle T r) =
      1 - operatorQuotientMap X convention T := by
  have he : operatorQuotientMap X convention T * operatorQuotientMap X convention T =
      operatorQuotientMap X convention T := by
    have hz := (operatorQuotientMap_eq_zero X convention _).mpr hT
    rwa [map_sub, operatorQuotientMap_mul, sub_eq_zero] at hz
  let q := quotientProjection (operatorIdeal X convention)
  calc
    operatorQuotientMap X convention (rieszCircle T r) = q (rieszCircle T r) := rfl
    _ = rieszCircle (operatorQuotientMap X convention T) r :=
      continuousLinearMap_rieszCircle q T (operatorQuotientMap X convention T) r hr0.le
        (resolvent_circleIntegrable T r hr0.le hcircle)
        (fun z hz => operatorQuotientMap_resolvent X convention T z (hcircle z hz))
    _ = 1 - operatorQuotientMap X convention T :=
      rieszCircle_of_idempotent _ he r hr0 hr1

theorem essential_rieszCircle_candidate_difference (T : BoundedOperators X)
    (hT : T * T - T ∈ operatorIdeal X convention) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ T) :
    (1 - rieszCircle T r) - T ∈ operatorIdeal X convention := by
  apply (operatorQuotientMap_eq_zero X convention _).mp
  rw [map_sub, map_sub, operatorQuotientMap_one,
    essential_rieszCircle_image X convention T hT r hr0 hr1 hcircle]
  abel

/-- The only additional fact needed to finish Lemma 2.4 after the contour
construction: idempotence of this actual Riesz integral. This helper does not
assert that missing analytic theorem. -/
theorem lift_idempotent_of_rieszCircle_idempotent (T : BoundedOperators X)
    (hT : T * T - T ∈ operatorIdeal X convention) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ T)
    (hE : rieszCircle T r * rieszCircle T r = rieszCircle T r) :
    ∃ P : BoundedOperators X, P * P = P ∧ P - T ∈ operatorIdeal X convention := by
  refine ⟨1 - rieszCircle T r, ?_,
    essential_rieszCircle_candidate_difference X convention T hT r hr0 hr1 hcircle⟩
  simp only [mul_sub, sub_mul, one_mul, mul_one, hE]
  abel

end NonCalkinAlgebra
