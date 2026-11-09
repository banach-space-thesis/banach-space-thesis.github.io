import NonCalkinAlgebra.ClosedTwistedAlgebra
import NonCalkinAlgebra.OrderedShiftChain

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderedTwistedAlgebra
open OrderedCocycle TwistedRegular CommutationChains
universe u
variable (Λ : Type u) [LinearOrder Λ]

/-- The concrete nonzero unital C*-algebra attached to a total order. -/
def algebra : ComplexCStarAlgebra.{u} := banachAlgebra (cocycle Λ)

def pair (ξ : Λ) : (algebra Λ).Carrier × (algebra Λ).Carrier :=
  (shiftInAlgebra (cocycle Λ) (u Λ ξ), shiftInAlgebra (cocycle Λ) (w Λ ξ 0))

theorem value_table (ξ η : Λ) :
    Value (pair Λ ξ) (pair Λ η) = if ξ < η then 0 else 1 :=
  OrderedShiftChain.value_table Λ ξ η

theorem isRelationChain : IsRelationChain Across (pair Λ) :=
  relationChain_of_value_table (pair Λ) (value_table Λ)

theorem first_selfAdjoint (ξ : Λ) : IsSelfAdjoint (pair Λ ξ).1 := by
  change star (shiftInAlgebra (cocycle Λ) (u Λ ξ)) = shiftInAlgebra (cocycle Λ) (u Λ ξ)
  apply Subtype.ext
  exact (selfAdjoint_shift_of_square (cocycle Λ) (u Λ ξ)
    (FiniteSupportCocycle.add_self_eq_zero _) (by simp)).star_eq

theorem second_selfAdjoint (ξ : Λ) : IsSelfAdjoint (pair Λ ξ).2 := by
  change star (shiftInAlgebra (cocycle Λ) (w Λ ξ 0)) = shiftInAlgebra (cocycle Λ) (w Λ ξ 0)
  apply Subtype.ext
  exact (selfAdjoint_shift_of_square (cocycle Λ) (w Λ ξ 0)
    (FiniteSupportCocycle.add_self_eq_zero _) (by simp)).star_eq

@[simp] theorem norm_first (ξ : Λ) : ‖(pair Λ ξ).1‖ = 1 := norm_shiftInAlgebra _ _
@[simp] theorem norm_second (ξ : Λ) : ‖(pair Λ ξ).2‖ = 1 := norm_shiftInAlgebra _ _

end NonCalkinAlgebra.OrderedTwistedAlgebra
