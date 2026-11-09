import NonCalkinAlgebra.CStarIdealApproximation
import NonCalkinAlgebra.AFCoefficientStatements

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u

instance complexCStarAlgebraStructure (D : ComplexCStarAlgebra.{u}) : CStarAlgebra D.Carrier where

variable {A : Type u} [CStarAlgebra A]

/-- Every closed two-sided ring ideal of a unital C*-algebra is self-adjoint.
Scalar closure and self-adjointness are not assumptions on the ideal. -/
theorem closed_twoSidedIdeal_star_mem (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A))
    {x : A} (hx : x ∈ I) : star x ∈ I := by
  change star x ∈ (I : Set A)
  rw [← hI.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨b, hb⟩ := exists_star_approximation x δ hδ
  have ha : star x * x ∈ I := I.mul_mem_left (star x) x hx
  refine ⟨(star x * x) * b * star x,
    I.mul_mem_right _ _ (I.mul_mem_right _ _ ha), ?_⟩
  simpa only [dist_eq_norm] using hb

/-- Simplicity when only closed self-adjoint two-sided ideals are considered. -/
def IsCStarSimple (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) →
    (∀ x ∈ I, star x ∈ I) → I = ⊥ ∨ I = ⊤

/-- The simplicity notions agree, proving the passage used in Remark 2.3. -/
theorem topologically_simple_iff_cstar_simple :
    IsTopologicallySimple A ↔ IsCStarSimple A := by
  constructor
  · intro h I hI _
    exact h I hI
  · intro h I hI
    exact h I hI (fun x hx => closed_twoSidedIdeal_star_mem I hI hx)

/-- The AF family-selection argument only needs simplicity in the usual
C*-sense; the closed-ring-ideal condition follows from automatic
self-adjointness. Abundance and Banach-algebra distinction remain explicit. -/
theorem AF_coefficient_existence_of_large_cstar_simple_family {J : Type}
    (D : J → ComplexCStarAlgebra.{0})
    (hlarge : Cardinal.continuum < Cardinal.mk J)
    (hdistinct : ∀ i j, Nonempty ((D i).Carrier ≃A[ℂ] (D j).Carrier) → i = j)
    (hAF : ∀ i, IsApproximatelyFiniteDimensional (D i).Carrier)
    (hdensity : ∀ i, HasDensityCharacter (D i).Carrier Cardinal.continuum)
    (hsimple : ∀ i, IsCStarSimple (D i).Carrier) :
    AFCoefficientExistenceStatement.{u} := by
  exact AF_coefficient_existence_of_large_family D hlarge hdistinct hAF hdensity
    (fun i => topologically_simple_iff_cstar_simple.mpr (hsimple i))

end NonCalkinAlgebra
