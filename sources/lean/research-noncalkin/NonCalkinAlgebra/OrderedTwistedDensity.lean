import NonCalkinAlgebra.OrderedTwistedAlgebra
import NonCalkinAlgebra.TwistedAlgebraDensity

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderedTwistedAlgebra
open OrderedCocycle

theorem u_injective {Λ : Type} [LinearOrder Λ] : Function.Injective (u Λ) := by
  intro ξ η h
  have h' := congrArg (fun g : OrderedCocycle.Group Λ => g.1.2) h
  exact Finsupp.single_left_injective (one_ne_zero : (1 : ZMod 2) ≠ 0) h'

theorem cardinal_coordinateGroup {Λ : Type} [LinearOrder Λ] [Infinite Λ]
    (hΛ : Cardinal.mk Λ = Cardinal.continuum) :
    Cardinal.mk (OrderedCocycle.Group Λ) = Cardinal.continuum := by
  have hnat : Cardinal.mk ℕ ≤ Cardinal.continuum := by
    simpa only [Cardinal.mk_nat] using Cardinal.aleph0_le_continuum
  have hindex : Cardinal.mk (Λ × ℕ) ≤ Cardinal.continuum :=
    cardinal_prod_le_continuum hΛ.le hnat
  have h2 : Cardinal.mk (ZMod 2) ≤ Cardinal.continuum :=
    (show Cardinal.mk (ZMod 2) ≤ Cardinal.aleph0 from Cardinal.mk_le_aleph0).trans
      Cardinal.aleph0_le_continuum
  have hV : Cardinal.mk ((Λ × ℕ) →₀ ZMod 2) ≤ Cardinal.continuum := by
    rw [Cardinal.mk_finsupp_of_infinite]
    exact max_le hindex h2
  have hU : Cardinal.mk (Λ →₀ ZMod 2) ≤ Cardinal.continuum := by
    rw [Cardinal.mk_finsupp_of_infinite]
    exact max_le hΛ.le h2
  apply le_antisymm
  · exact cardinal_prod_le_continuum (cardinal_prod_le_continuum hV hU) hV
  · rw [← hΛ]
    exact Cardinal.mk_le_of_injective u_injective

/-- The concrete C*-algebra associated to a continuum-sized total order
has the exact density required by the coefficient theorem. -/
theorem density_continuum {Λ : Type} [LinearOrder Λ] [Infinite Λ]
    (hΛ : Cardinal.mk Λ = Cardinal.continuum) :
    HasDensityCharacter (algebra Λ).Carrier Cardinal.continuum :=
  TwistedRegular.density_continuum (cocycle Λ) (cardinal_coordinateGroup hΛ)

end NonCalkinAlgebra.OrderedTwistedAlgebra
