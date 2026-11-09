import NonCalkinAlgebra.RealOperatorIdeals
import NonCalkinAlgebra.Statements

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u v

structure RealBanachAlgebra where
  Carrier : Type u
  [normedRing : NormedRing Carrier]
  [normedAlgebra : NormedAlgebra ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]
  [nontrivial : Nontrivial Carrier]

attribute [instance] RealBanachAlgebra.normedRing RealBanachAlgebra.normedAlgebra
  RealBanachAlgebra.completeSpace RealBanachAlgebra.nontrivial

/-- Forgetting complex scalar multiplication changes neither the normed
ring nor its underlying set or topology. -/
def underlyingRealBanachAlgebra (A : ComplexBanachAlgebra.{u}) : RealBanachAlgebra.{u} where
  Carrier := A.Carrier

theorem underlying_real_density (A : ComplexBanachAlgebra.{u}) (κ : Cardinal.{u})
    (h : HasDensityCharacter A.Carrier κ) :
    HasDensityCharacter (underlyingRealBanachAlgebra A).Carrier κ := h

/-- `TwoSidedIdeal` is a ring ideal. In a unital complex algebra, multiplication
by the central scalar i1 already gives closure under i. Thus the ideal
condition used in Main is literally unchanged on the underlying real algebra. -/
theorem underlying_real_ideal_structure (A : ComplexBanachAlgebra.{u})
    (h : HasExactlyOneNonzeroProperClosedIdeal A.Carrier) :
    HasExactlyOneNonzeroProperClosedIdeal (underlyingRealBanachAlgebra A).Carrier := h

structure RealOperatorQuotientIso (X : Type v)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (k : QuotientConvention) (A : Type u) [NormedRing A] [NormedAlgebra ℝ A]
    extends RealOperatorQuotient X k ≃L[ℝ] A where
  map_mul_representatives : ∀ S T : X →L[ℝ] X,
    toContinuousLinearEquiv (realOperatorQuotientMap X k (S * T)) =
      toContinuousLinearEquiv (realOperatorQuotientMap X k S) *
        toContinuousLinearEquiv (realOperatorQuotientMap X k T)
  map_one_representative : toContinuousLinearEquiv (realOperatorQuotientMap X k 1) = 1

/-- The real analogue asserted in Remark 1.2. This is a separate target,
not a renaming of the complex theorem. -/
def RealMainStatement : Prop :=
  ∃ A : RealBanachAlgebra.{0},
    HasDensityCharacter A.Carrier Cardinal.continuum ∧
    HasExactlyOneNonzeroProperClosedIdeal A.Carrier ∧
    ∀ (k : QuotientConvention) (X : Type v)
      [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
      ¬ Nonempty (RealOperatorQuotientIso X k A.Carrier)

end NonCalkinAlgebra
