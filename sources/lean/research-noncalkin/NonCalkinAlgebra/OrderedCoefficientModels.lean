import NonCalkinAlgebra.OrderedTwistedStructure
import NonCalkinAlgebra.OrderedTwistedDensity
import NonCalkinAlgebra.OrderedTwistedSkeleton
import Mathlib.Analysis.Real.Cardinality

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderedTwistedAlgebra
open CommutationChains

/-- The analytic and commutation properties of each concrete coefficient
candidate. This does not assert pairwise nonisomorphism of the candidates. -/
theorem continuum_model_properties {Λ : Type} [LinearOrder Λ] [Infinite Λ]
    (hΛ : Cardinal.mk Λ = Cardinal.continuum) :
    NonCalkinAlgebra.IsApproximatelyFiniteDimensional (algebra Λ).Carrier ∧
    HasDensityCharacter (algebra Λ).Carrier Cardinal.continuum ∧
    NonCalkinAlgebra.IsTopologicallySimple (algebra Λ).Carrier ∧
    IsRelationChain Across (pair Λ) ∧ WeaklySkeletonLike Across (pair Λ) :=
  ⟨isApproximatelyFiniteDimensional Λ, density_continuum hΛ,
    isTopologicallySimple Λ, isRelationChain Λ, weaklySkeletonLike Λ⟩

/-- A concrete simple unital AF C*-algebra of density continuum exists.
Avoidance of the separable Calkin models is a further, unproved requirement. -/
theorem exists_simple_AF_continuum :
    ∃ D : ComplexCStarAlgebra.{0},
      NonCalkinAlgebra.IsApproximatelyFiniteDimensional D.Carrier ∧
      HasDensityCharacter D.Carrier Cardinal.continuum ∧
      NonCalkinAlgebra.IsTopologicallySimple D.Carrier := by
  exact ⟨algebra ℝ, isApproximatelyFiniteDimensional ℝ,
    density_continuum Cardinal.mk_real, isTopologicallySimple ℝ⟩

end NonCalkinAlgebra.OrderedTwistedAlgebra
