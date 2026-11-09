import BanachIsometric.QuaternionicPolarization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The genuine real Euclidean norm on a finite right quaternionic space.
The scalar action is the existing opposite-module right multiplication.
An actual real linear isometry identifies it with its 4m real coordinates. -/

namespace BanachIsometric.Quaternionic

open scoped Quaternion

noncomputable section

abbrev Euclidean (m : ℕ) := PiLp 2 (fun _ : Fin m => H)

def scalarOppositeEquiv : H ≃ₗ[Hᵐᵒᵖ] Hᵐᵒᵖ where
  toFun := MulOpposite.op
  invFun := MulOpposite.unop
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def scalarCoordinates (m : ℕ) : Euclidean m ≃ₗ[Hᵐᵒᵖ] (Fin m → Hᵐᵒᵖ) :=
  (WithLp.linearEquiv 2 Hᵐᵒᵖ (Fin m → H)).trans
    (LinearEquiv.piCongrRight fun _ => scalarOppositeEquiv)

instance (m : ℕ) : FiniteDimensional Hᵐᵒᵖ (Euclidean m) :=
  FiniteDimensional.of_injective (scalarCoordinates m).toLinearMap (scalarCoordinates m).injective

def realCoordinateIndex (m : ℕ) : (Σ _ : Fin m, Fin 4) ≃ Fin (4 * m) :=
  Fintype.equivOfCardEq (by simp [Nat.mul_comm])

def realCoordinateIsometry (m : ℕ) : Euclidean m ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (4 * m)) :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin m => Quaternion.linearIsometryEquivTuple)).trans
    ((LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin m) (_ : Fin 4) => ℝ)).symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (realCoordinateIndex m)))

theorem finrank_right_euclidean (m : ℕ) : Module.finrank Hᵐᵒᵖ (Euclidean m) = m := by
  rw [(scalarCoordinates m).finrank_eq]
  simp

theorem finrank_real_euclidean (m : ℕ) : Module.finrank ℝ (Euclidean m) = 4 * m := by
  rw [(realCoordinateIsometry m).toLinearEquiv.finrank_eq]
  simp

theorem finrank_real_opposite : Module.finrank ℝ Hᵐᵒᵖ = 4 := by
  rw [← (MulOpposite.opLinearEquiv ℝ (M := H)).finrank_eq]
  exact Quaternion.finrank_eq_four

theorem rightMul_apply (m : ℕ) (x : Euclidean m) (a : H) (r : Fin m) :
    rightMul x a r = x r * a := rfl

theorem norm_rightMul (m : ℕ) (x : Euclidean m) (a : H) : ‖rightMul x a‖ = ‖x‖ * ‖a‖ := by
  simpa only [rightMul, MulOpposite.norm_op, mul_comm] using norm_smul (MulOpposite.op a) x

theorem norm_sq_euclidean (m : ℕ) (x : Euclidean m) : ‖x‖ ^ 2 = ∑ r, ‖x r‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 (fun _ : Fin m => H) x

end
end BanachIsometric.Quaternionic
