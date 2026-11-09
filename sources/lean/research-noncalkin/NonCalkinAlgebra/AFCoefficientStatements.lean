import NonCalkinAlgebra.CoefficientCounting
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.StarSubalgebra

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open TopologicalSpace SurveyStatements.P2
universe u v

/-- A nonzero unital complex C*-algebra. Its Banach algebra, involution,
conjugate-linearity and C*-norm identity are all actual structures. -/
structure ComplexCStarAlgebra extends ComplexBanachAlgebra.{u} where
  [starRing : StarRing Carrier]
  [cstarRing : CStarRing Carrier]
  [starModule : StarModule ℂ Carrier]

attribute [instance] ComplexCStarAlgebra.starRing
  ComplexCStarAlgebra.cstarRing ComplexCStarAlgebra.starModule

/-- AF in the directed-limit sense, valid without separability: a directed
family of finite-dimensional unital *-subalgebras has dense union. The
indexing family is not required to be a sequence. -/
def IsApproximatelyFiniteDimensional (A : Type u) [NormedRing A]
    [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A] : Prop :=
  ∃ S : Set (StarSubalgebra ℂ A), S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧
    (∀ B ∈ S, FiniteDimensional ℂ B) ∧ Dense (⋃ B ∈ S, (B : Set A))

/-- The full AF coefficient target, Theorem 2.2 together with Remark 2.3.
This proposition is not asserted as a proved theorem. -/
def AFCoefficientExistenceStatement : Prop :=
  ∃ D : ComplexCStarAlgebra.{0},
    IsApproximatelyFiniteDimensional D.Carrier ∧
    HasDensityCharacter D.Carrier Cardinal.continuum ∧
    IsTopologicallySimple D.Carrier ∧
    ∀ (k : QuotientConvention) (Y : Type v)
      [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] [SeparableSpace Y],
      ¬ Nonempty (OperatorQuotientIso Y k D.Carrier)

/-- Forgetting the involution and AF structure gives exactly the coefficient
input used by the construction; the C*-identity supplies norm of the unit. -/
theorem coefficient_existence_of_AF (h : AFCoefficientExistenceStatement.{v}) :
    CoefficientExistenceStatement.{v} := by
  obtain ⟨D, hAF, hdensity, hsimple, havoid⟩ := h
  exact ⟨D.toComplexBanachAlgebra, norm_one, hdensity, hsimple, havoid⟩

/-- Cardinal selection retains the AF and C* structure of the chosen member.
The abundance of such a family and its distinction as Banach algebras are
explicit hypotheses, still requiring the Farah--Katsura/Gardner foundations. -/
theorem AF_coefficient_existence_of_large_family {I : Type}
    (D : I → ComplexCStarAlgebra.{0})
    (hlarge : Cardinal.continuum < Cardinal.mk I)
    (hdistinct : ∀ i j, Nonempty ((D i).Carrier ≃A[ℂ] (D j).Carrier) → i = j)
    (hAF : ∀ i, IsApproximatelyFiniteDimensional (D i).Carrier)
    (hdensity : ∀ i, HasDensityCharacter (D i).Carrier Cardinal.continuum)
    (hsimple : ∀ i, IsTopologicallySimple (D i).Carrier) :
    AFCoefficientExistenceStatement.{v} := by
  obtain ⟨i, hi⟩ := exists_member_avoiding_separable_models
    (fun i => (D i).toComplexBanachAlgebra) hlarge hdistinct
  refine ⟨D i, hAF i, hdensity i, hsimple i, ?_⟩
  intro k Y _ _ _ _
  rintro ⟨iso⟩
  obtain ⟨M, ⟨e⟩⟩ := exists_separableCalkinModel k Y
  exact hi M ⟨e.trans iso.toContinuousAlgEquiv⟩

end NonCalkinAlgebra
