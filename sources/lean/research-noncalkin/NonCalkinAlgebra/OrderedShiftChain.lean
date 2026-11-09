import NonCalkinAlgebra.OrderedCocycle
import NonCalkinAlgebra.TwistedRegularCommutators
import NonCalkinAlgebra.CommutationChains

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderedShiftChain
open OrderedCocycle TwistedRegular CommutationChains
universe u
variable (Λ : Type u) [LinearOrder Λ]

/-- The actual bounded-operator pairs carrying the order relation. -/
def pair (ξ : Λ) :
    (SquareSummable (OrderedCocycle.Group Λ) →L[ℂ] SquareSummable (OrderedCocycle.Group Λ)) ×
    (SquareSummable (OrderedCocycle.Group Λ) →L[ℂ] SquareSummable (OrderedCocycle.Group Λ)) :=
  (shift (cocycle Λ) (u Λ ξ), shift (cocycle Λ) (w Λ ξ 0))

/-- The exact 0/1 commutator table on arbitrary total orders, with no
endpoint or countability restriction and with a noncommuting diagonal. -/
theorem value_table (ξ η : Λ) :
    Value (pair Λ ξ) (pair Λ η) = if ξ < η then 0 else 1 := by
  change (1 / 2 : ℝ) * ‖shift (cocycle Λ) (u Λ ξ) * shift (cocycle Λ) (w Λ η 0) -
    shift (cocycle Λ) (w Λ η 0) * shift (cocycle Λ) (u Λ ξ)‖ = _
  by_cases h : ξ < η
  · rw [if_pos h]
    apply commutator_value_eq_zero
    · simp [not_le.mpr h]
    · simp
  · rw [if_neg h]
    apply commutator_value_eq_one
    · simp [le_of_not_gt h]
    · simp

theorem isRelationChain : IsRelationChain Across (pair Λ) :=
  relationChain_of_value_table (pair Λ) (value_table Λ)

theorem pair_injective : Function.Injective (pair Λ) := by
  intro ξ η heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨hyes, hno⟩ := (isRelationChain Λ ξ η).mp hlt
    exact hno (by simpa only [heq] using hyes)
  · obtain ⟨hyes, hno⟩ := (isRelationChain Λ η ξ).mp hgt
    exact hno (by simpa only [heq] using hyes)

end NonCalkinAlgebra.OrderedShiftChain
