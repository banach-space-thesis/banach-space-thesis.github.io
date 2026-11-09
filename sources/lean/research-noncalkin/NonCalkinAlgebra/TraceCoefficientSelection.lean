import NonCalkinAlgebra.AFCoefficientStatements

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open TopologicalSpace
universe u v w

/-- A normalized bounded complex trace. Positivity is unnecessary for
transport along a Banach algebra isomorphism. -/
def IsNormalizedTrace {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    (τ : A →L[ℂ] ℂ) : Prop :=
  τ 1 = 1 ∧ ∀ a b : A, τ (a * b) = τ (b * a)

def idempotentTraceValues {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    (τ : A →L[ℂ] ℂ) : Set ℂ :=
  {z | ∃ p : A, p * p = p ∧ τ p = z}

section Transport

variable {A : Type u} {B : Type w}
  [NormedRing A] [NormedAlgebra ℂ A] [NormedRing B] [NormedAlgebra ℂ B]

theorem isNormalizedTrace_comp (e : A ≃A[ℂ] B) {τ : B →L[ℂ] ℂ}
    (hτ : IsNormalizedTrace τ) :
    IsNormalizedTrace (τ.comp (continuousAlgEquivToLinear e).toContinuousLinearMap) := by
  constructor
  · change τ (e 1) = 1
    rw [map_one]
    exact hτ.1
  · intro a b
    change τ (e (a * b)) = τ (e (b * a))
    simp only [map_mul]
    exact hτ.2 _ _

theorem idempotentTraceValues_comp (e : A ≃A[ℂ] B) (τ : B →L[ℂ] ℂ) :
    idempotentTraceValues (τ.comp (continuousAlgEquivToLinear e).toContinuousLinearMap) =
      idempotentTraceValues τ := by
  ext z
  constructor
  · rintro ⟨p, hp, hz⟩
    exact ⟨e p, by rw [← map_mul, hp], hz⟩
  · rintro ⟨q, hq, hz⟩
    refine ⟨e.symm q, by rw [← map_mul, hq], ?_⟩
    change τ (e (e.symm q)) = z
    simpa only [e.apply_symm_apply] using hz

theorem idempotentTraceValues_eq_of_unique (e : A ≃A[ℂ] B)
    (σ : A →L[ℂ] ℂ) (τ : B →L[ℂ] ℂ)
    (hσ : ∀ ψ, IsNormalizedTrace ψ → ψ = σ) (hτ : IsNormalizedTrace τ) :
    idempotentTraceValues σ = idempotentTraceValues τ := by
  rw [← hσ _ (isNormalizedTrace_comp e hτ)]
  exact idempotentTraceValues_comp e τ

end Transport

/-- Distinct subsets can be distinguished by their traces of idempotents.
The trace realization and the exclusion of the other parameter values
are separate construction hypotheses. -/
theorem AF_coefficient_existence_of_idempotent_trace_codes {J : Type}
    (hJ : Cardinal.mk J = Cardinal.continuum) (θ : J → ℂ)
    (D : Set J → ComplexCStarAlgebra.{0})
    (τ : ∀ S, (D S).Carrier →L[ℂ] ℂ)
    (hτ : ∀ S, IsNormalizedTrace (τ S))
    (hunique : ∀ S ψ, IsNormalizedTrace ψ → ψ = τ S)
    (hcode : ∀ S i, θ i ∈ idempotentTraceValues (τ S) ↔ i ∈ S)
    (hAF : ∀ S, IsApproximatelyFiniteDimensional (D S).Carrier)
    (hdensity : ∀ S, HasDensityCharacter (D S).Carrier Cardinal.continuum)
    (hsimple : ∀ S, IsTopologicallySimple (D S).Carrier) :
    AFCoefficientExistenceStatement.{v} := by
  apply AF_coefficient_existence_of_large_family D _ _ hAF hdensity hsimple
  · rw [Cardinal.mk_set, hJ]
    exact Cardinal.cantor _
  · intro S T h
    obtain ⟨e⟩ := h
    have he := idempotentTraceValues_eq_of_unique e (τ S) (τ T) (hunique S) (hτ T)
    ext i
    rw [← hcode S i, ← hcode T i, he]


section Universal
variable {A : Type u} {B : Type v}
  [NormedRing A] [NormedAlgebra ℂ A] [NormedRing B] [NormedAlgebra ℂ B]

/-- Values of single idempotents on which every continuous normalized trace agrees. -/
def commonIdempotentTraceValues (A : Type u) [NormedRing A] [NormedAlgebra ℂ A] : Set ℂ :=
  {z | ∃ p : A, p * p = p ∧ ∀ τ : A →L[ℂ] ℂ, IsNormalizedTrace τ → τ p = z}

theorem commonIdempotentTraceValues_congr (e : A ≃A[ℂ] B) :
    commonIdempotentTraceValues A = commonIdempotentTraceValues B := by
  ext z
  constructor
  · rintro ⟨p, hp, hz⟩
    refine ⟨e p, by rw [← map_mul, hp], fun τ hτ => ?_⟩
    exact hz _ (isNormalizedTrace_comp e hτ)
  · rintro ⟨p, hp, hz⟩
    refine ⟨e.symm p, by rw [← map_mul, hp], fun τ hτ => ?_⟩
    exact hz _ (isNormalizedTrace_comp e.symm hτ)

end Universal

/-- Each positive code can be witnessed by an idempotent in one factor.
Excluding a negative code only requires one normalized trace on the product. -/
theorem AF_coefficient_existence_of_common_trace_codes {J : Type}
    (hJ : Cardinal.mk J = Cardinal.continuum) (θ : J → ℂ)
    (D : Set J → ComplexCStarAlgebra.{0})
    (hcode : ∀ S i, θ i ∈ commonIdempotentTraceValues (D S).Carrier ↔ i ∈ S)
    (hAF : ∀ S, IsApproximatelyFiniteDimensional (D S).Carrier)
    (hdensity : ∀ S, HasDensityCharacter (D S).Carrier Cardinal.continuum)
    (hsimple : ∀ S, IsTopologicallySimple (D S).Carrier) :
    AFCoefficientExistenceStatement.{v} := by
  apply AF_coefficient_existence_of_large_family D _ _ hAF hdensity hsimple
  · rw [Cardinal.mk_set, hJ]
    exact Cardinal.cantor _
  · intro S T h
    obtain ⟨e⟩ := h
    have he := commonIdempotentTraceValues_congr e
    ext i
    rw [← hcode S i, ← hcode T i, he]

end NonCalkinAlgebra
