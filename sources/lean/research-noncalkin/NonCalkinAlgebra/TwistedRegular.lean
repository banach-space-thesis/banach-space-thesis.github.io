import NonCalkinAlgebra.BinaryPhase
import NonCalkinAlgebra.WeightedPermutation
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Abel

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
open BinaryPhase
universe u
variable {G : Type u} [AddCommGroup G]

/-- A biadditive binary cocycle. Biadditivity implies the cocycle identity
used by the signed regular representation. -/
abbrev Cocycle (G : Type u) [AddCommGroup G] := G →+ G →+ ZMod 2

def translation (g : G) : G ≃ G where
  toFun h := h - g
  invFun h := h + g
  left_inv h := sub_add_cancel h g
  right_inv h := add_sub_cancel_right h g

/-- The actual bounded operator L_g on l2(G): L_g e_h = sign(c(g,h)) e_(g+h). -/
def shift (c : Cocycle G) (g : G) : SquareSummable G →L[ℂ] SquareSummable G :=
  (weightedPermutation (translation g) (fun h => phase (c g (h - g)))
    (fun _ => norm_phase _)).toContinuousLinearMap

@[simp] theorem shift_apply (c : Cocycle G) (g : G) (f : SquareSummable G) (h : G) :
    shift c g f h = phase (c g (h - g)) * f (h - g) := rfl

@[simp] theorem norm_shift_apply (c : Cocycle G) (g : G) (f : SquareSummable G) :
    ‖shift c g f‖ = ‖f‖ :=
  (weightedPermutation (translation g) (fun h => phase (c g (h - g)))
    (fun _ => norm_phase _)).norm_map f

@[simp] theorem shift_zero (c : Cocycle G) : shift c 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext h
  simp [shift_apply]

theorem cocycle_step (c : Cocycle G) (g k h : G) :
    c g (h - g) + c k (h - (g + k)) = c g k + c (g + k) (h - (g + k)) := by
  have ht : h - g = k + (h - (g + k)) := by abel
  rw [ht, map_add, map_add, AddMonoidHom.add_apply]
  abel

/-- The twisted multiplication law is an equality of actual bounded operators. -/
theorem shift_mul (c : Cocycle G) (g k : G) :
    shift c g * shift c k = phase (c g k) • shift c (g + k) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext h
  change phase (c g (h - g)) * (phase (c k (h - g - k)) * f (h - g - k)) =
    phase (c g k) * (phase (c (g + k) (h - (g + k))) * f (h - (g + k)))
  have ht : h - g - k = h - (g + k) := by abel
  rw [ht]
  calc
    _ = phase (c g (h - g) + c k (h - (g + k))) * f (h - (g + k)) := by
      rw [phase_add, mul_assoc]
    _ = phase (c g k + c (g + k) (h - (g + k))) * f (h - (g + k)) := by
      rw [cocycle_step]
    _ = _ := by rw [phase_add, mul_assoc]

theorem shift_single_zero [DecidableEq G] (c : Cocycle G) (g : G) :
    shift c g (lp.single (E := fun _ : G => ℂ) 2 0 (1 : ℂ)) =
      lp.single (E := fun _ : G => ℂ) 2 g (1 : ℂ) := by
  classical
  apply lp.ext
  funext h
  change phase (c g (h - g)) * (Pi.single (0 : G) (1 : ℂ) : G → ℂ) (h - g) =
    (Pi.single g (1 : ℂ) : G → ℂ) h
  by_cases hh : h = g
  · subst h
    have hgg : g - g = 0 := sub_self g
    rw [hgg]
    simp
  · have hsub : h - g ≠ 0 := sub_ne_zero.mpr hh
    simp only [Pi.single_eq_of_ne hsub, Pi.single_eq_of_ne hh, mul_zero]

theorem shift_injective (c : Cocycle G) : Function.Injective (shift c) := by
  classical
  intro g h heq
  by_contra hgh
  have hv := congrArg (fun T : SquareSummable G →L[ℂ] SquareSummable G =>
    T (lp.single 2 0 (1 : ℂ))) heq
  dsimp only at hv
  rw [shift_single_zero, shift_single_zero] at hv
  have hx := congrArg (fun f : SquareSummable G => f g) hv
  exact one_ne_zero (by
    simpa only [lp.coeFn_single, Pi.single_eq_same, Pi.single_eq_of_ne hgh] using hx)

instance squareSummable_nontrivial : Nontrivial (SquareSummable G) := by
  classical
  refine ⟨⟨lp.single 2 (0 : G) (1 : ℂ), 0, ?_⟩⟩
  intro h
  have hx := congrArg (fun f : SquareSummable G => f 0) h
  exact one_ne_zero (by simpa only [lp.coeFn_single, Pi.single_eq_same,
    lp.coeFn_zero, Pi.zero_apply] using hx)

@[simp] theorem norm_shift (c : Cocycle G) (g : G) : ‖shift c g‖ = 1 :=
  (weightedPermutation (translation g) (fun h => phase (c g (h - g)))
    (fun _ => norm_phase _)).norm_toContinuousLinearMap

theorem shift_commutation (c : Cocycle G) (g k : G) :
    shift c g * shift c k = phase (c g k + c k g) • (shift c k * shift c g) := by
  rw [shift_mul, shift_mul, smul_smul, add_comm k g, phase_add]
  simp only [mul_assoc, phase_mul_self, mul_one]

@[simp] theorem norm_shift_mul (c : Cocycle G) (g k : G) :
    ‖shift c g * shift c k‖ = 1 := by
  rw [shift_mul, norm_smul, norm_phase, norm_shift, one_mul]

end NonCalkinAlgebra.TwistedRegular
