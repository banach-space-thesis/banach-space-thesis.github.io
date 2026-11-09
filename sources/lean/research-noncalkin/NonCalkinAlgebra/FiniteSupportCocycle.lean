import NonCalkinAlgebra.TwistedRegular
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Prod

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.FiniteSupportCocycle
universe u v w

/-- A matrix on arbitrary index sets extends to an actual bilinear pairing
of the finite-support vector spaces. Every sum in this definition is finite. -/
def pairing {I : Type u} {J : Type v} (m : I → J → ZMod 2) :
    (I →₀ ZMod 2) →ₗ[ZMod 2] (J →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (fun i =>
    Finsupp.linearCombination (ZMod 2) (m i))

@[simp] theorem pairing_single_single {I : Type u} {J : Type v}
    (m : I → J → ZMod 2) (i : I) (j : J) (a b : ZMod 2) :
    pairing m (Finsupp.single i a) (Finsupp.single j b) = a * (b * m i j) := by
  simp [pairing, Finsupp.linearCombination_single, smul_eq_mul]

/-- Regard an arbitrary bilinear X-Y pairing as the binary cocycle on X×Y
which has nonzero entries only from the X coordinates to the Y coordinates. -/
def ofPairing {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    [Module (ZMod 2) X] [Module (ZMod 2) Y]
    (B : X →ₗ[ZMod 2] Y →ₗ[ZMod 2] ZMod 2) : TwistedRegular.Cocycle (X × Y) where
  toFun x :=
    { toFun y := B x.1 y.2
      map_zero' := by simp
      map_add' y z := by simp }
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

@[simp] theorem ofPairing_apply {X : Type u} {Y : Type v}
    [AddCommGroup X] [AddCommGroup Y] [Module (ZMod 2) X] [Module (ZMod 2) Y]
    (B : X →ₗ[ZMod 2] Y →ₗ[ZMod 2] ZMod 2) (x y : X × Y) :
    ofPairing B x y = B x.1 y.2 := rfl

theorem add_self_eq_zero {X : Type u} [AddCommGroup X] [Module (ZMod 2) X] (x : X) :
    x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h : (2 : ZMod 2) • x = 0 := by rw [h2, zero_smul]
  simpa only [two_smul] using h

end NonCalkinAlgebra.FiniteSupportCocycle
