import NonCalkinAlgebra.RieszCircleIdempotence
import NonCalkinAlgebra.RieszCircleQuotient
import NonCalkinAlgebra.PrerequisiteStatements

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2 Metric
universe v

/-- Lemma 2.4 under either quotient convention, on arbitrary complex Banach
spaces. The projection is 1 minus the actual normalized Riesz integral. -/
theorem lift_essential_idempotent (X : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (convention : QuotientConvention) (T : BoundedOperators X)
    (hT : T * T - T ∈ operatorIdeal X convention) :
    ∃ P : BoundedOperators X, P * P = P ∧ P - T ∈ operatorIdeal X convention := by
  obtain ⟨r, hr0, hr1, hcircle⟩ := essential_idempotent_resolvent_circle X convention T hT
  have hc : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ T := by
    intro z hz
    exact hcircle z (by simpa only [mem_sphere, dist_zero_right] using hz)
  exact lift_idempotent_of_rieszCircle_idempotent X convention T hT r hr0 hr1 hc
    (rieszCircle_isIdempotent T r hr0 hc)

theorem idempotent_lifting : IdempotentLiftingStatement.{v} := by
  intro convention X _ _ _ T hT
  exact lift_essential_idempotent X convention T hT

end NonCalkinAlgebra
