import NonCalkinAlgebra.FiniteSupportCocycle

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderedCocycle
open FiniteSupportCocycle
universe u
variable (Λ : Type u) [LinearOrder Λ]

/-- Three independent families of binary finite-support coordinates. -/
abbrev Group := (((Λ × ℕ) →₀ ZMod 2) × (Λ →₀ ZMod 2)) × ((Λ × ℕ) →₀ ZMod 2)

def diagonal (i j : Λ × ℕ) : ZMod 2 := if i = j then 1 else 0
def orderEntry (ξ : Λ) (j : Λ × ℕ) : ZMod 2 := if j.1 ≤ ξ then 1 else 0

def crossPairing :
    (((Λ × ℕ) →₀ ZMod 2) × (Λ →₀ ZMod 2)) →ₗ[ZMod 2]
      ((Λ × ℕ) →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (pairing (diagonal Λ)).coprod (pairing (orderEntry Λ))

/-- The order-dependent binary cocycle, with genuine finite-support sums. -/
def cocycle : TwistedRegular.Cocycle (Group Λ) := ofPairing (crossPairing Λ)

def v (ξ : Λ) (n : ℕ) : Group Λ := ((Finsupp.single (ξ, n) 1, 0), 0)
def u (ξ : Λ) : Group Λ := ((0, Finsupp.single ξ 1), 0)
def w (ξ : Λ) (n : ℕ) : Group Λ := ((0, 0), Finsupp.single (ξ, n) 1)

@[simp] theorem cocycle_v_w (ξ η : Λ) (n m : ℕ) :
    cocycle Λ (v Λ ξ n) (w Λ η m) = if (ξ, n) = (η, m) then 1 else 0 := by
  simp [cocycle, v, w, crossPairing, diagonal]

@[simp] theorem cocycle_u_w (ξ η : Λ) (n : ℕ) :
    cocycle Λ (u Λ ξ) (w Λ η n) = if η ≤ ξ then 1 else 0 := by
  simp [cocycle, u, w, crossPairing, orderEntry]

@[simp] theorem cocycle_w_left (ξ : Λ) (n : ℕ) (a : Group Λ) :
    cocycle Λ (w Λ ξ n) a = 0 := by
  simp [cocycle, w, crossPairing]

@[simp] theorem cocycle_v_right (a : Group Λ) (ξ : Λ) (n : ℕ) :
    cocycle Λ a (v Λ ξ n) = 0 := by
  simp [cocycle, v]

@[simp] theorem cocycle_u_right (a : Group Λ) (ξ : Λ) :
    cocycle Λ a (u Λ ξ) = 0 := by
  simp [cocycle, u]

end NonCalkinAlgebra.OrderedCocycle
