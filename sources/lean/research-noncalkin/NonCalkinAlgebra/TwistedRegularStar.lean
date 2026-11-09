import NonCalkinAlgebra.TwistedRegular
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Classes

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
open BinaryPhase
universe u
variable {G : Type u} [AddCommGroup G]

instance operatorCStarAlgebra :
    CStarAlgebra (SquareSummable G →L[ℂ] SquareSummable G) where

/-- Isometry gives the actual Hilbert-space adjoint identity. -/
theorem star_shift_mul_self (c : Cocycle G) (g : G) :
    star (shift c g) * shift c g = 1 := by
  change ContinuousLinearMap.adjoint (shift c g) ∘L shift c g = 1
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (shift c g)).mp
    (norm_shift_apply c g)

theorem shift_mul_inverse (c : Cocycle G) (g : G) :
    shift c g * (phase (c g (-g)) • shift c (-g)) = 1 := by
  rw [mul_smul_comm, shift_mul, smul_smul, phase_mul_self,
    add_neg_cancel, shift_zero, one_smul]

/-- Adjoint formula for the concrete twisted regular operators. -/
theorem star_shift (c : Cocycle G) (g : G) :
    star (shift c g) = phase (c g (-g)) • shift c (-g) := by
  calc
    star (shift c g) = star (shift c g) * 1 := (mul_one _).symm
    _ = star (shift c g) * (shift c g * (phase (c g (-g)) • shift c (-g))) := by
      rw [shift_mul_inverse]
    _ = (star (shift c g) * shift c g) * (phase (c g (-g)) • shift c (-g)) :=
      (mul_assoc _ _ _).symm
    _ = _ := by rw [star_shift_mul_self, one_mul]

theorem shift_mul_star_self (c : Cocycle G) (g : G) :
    shift c g * star (shift c g) = 1 := by
  rw [star_shift]
  exact shift_mul_inverse c g

theorem selfAdjoint_shift_of_square (c : Cocycle G) (g : G)
    (hg : g + g = 0) (hc : c g g = 0) : IsSelfAdjoint (shift c g) := by
  have hsq : shift c g * shift c g = 1 := by
    rw [shift_mul, hg, hc, phase_zero, shift_zero, one_smul]
  change star (shift c g) = shift c g
  calc
    star (shift c g) = star (shift c g) * 1 := (mul_one _).symm
    _ = star (shift c g) * (shift c g * shift c g) := by rw [hsq]
    _ = (star (shift c g) * shift c g) * shift c g := (mul_assoc _ _ _).symm
    _ = _ := by rw [star_shift_mul_self, one_mul]

end NonCalkinAlgebra.TwistedRegular
