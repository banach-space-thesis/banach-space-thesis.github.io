import NonCalkinAlgebra.OrderedTwistedAlgebra
import NonCalkinAlgebra.OrderedCocycleNondegenerate
import NonCalkinAlgebra.TwistedSimplicity
import NonCalkinAlgebra.TwistedAF

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderedTwistedAlgebra
universe u
variable (Λ : Type u) [LinearOrder Λ]

/-- AF is proved for the actual operator algebra, for every indexing order. -/
theorem isApproximatelyFiniteDimensional :
    NonCalkinAlgebra.IsApproximatelyFiniteDimensional (algebra Λ).Carrier :=
  TwistedRegular.isApproximatelyFiniteDimensional (OrderedCocycle.cocycle Λ)

/-- Every nonzero finite binary coordinate has a noncommuting coordinate. -/
theorem exists_noncommuting_coordinate (g : OrderedCocycle.Group Λ) (hg : g ≠ 0) :
    ∃ h : OrderedCocycle.Group Λ,
      OrderedCocycle.cocycle Λ h g + OrderedCocycle.cocycle Λ g h ≠ 0 := by
  by_contra! hall
  apply hg
  apply OrderedCocycle.alternating_nondegenerate Λ g
  intro h
  simpa only [OrderedCocycle.alternating, add_comm] using hall h

/-- Simplicity follows from the proved alternating nondegeneracy and the
contractive averaging argument in the concrete norm-closed algebra. -/
theorem isTopologicallySimple : NonCalkinAlgebra.IsTopologicallySimple (algebra Λ).Carrier :=
  TwistedRegular.isTopologicallySimple_of_nondegenerate (OrderedCocycle.cocycle Λ)
    (exists_noncommuting_coordinate Λ)

end NonCalkinAlgebra.OrderedTwistedAlgebra
