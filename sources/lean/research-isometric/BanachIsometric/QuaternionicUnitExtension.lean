import BanachIsometric.QuaternionicHermitianSplitting

/-! An isometry between scalar-orthogonal kernels extends over the chosen
unit quaternionic lines. All coordinates and inverses are actual Hopp-linear
maps; the exact norm-square splitting proves norm preservation. -/

namespace BanachIsometric.Quaternionic

noncomputable section

structure UnitHermitianData (V : Type*) [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] where
  hermitian : HermitianForm V
  diagonal : ∀ x, hermitian.form x x = (‖x‖ ^ 2 : ℝ)
  unit : V
  unit_norm : ‖unit‖ = 1

namespace UnitHermitianData

variable {V W : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V]
    [NormedAddCommGroup W] [Module Hᵐᵒᵖ W]
    (D : UnitHermitianData V) (E : UnitHermitianData W)

abbrev kernel : Submodule Hᵐᵒᵖ V := D.hermitian.unitKernel D.unit
abbrev scalar : V →ₗ[Hᵐᵒᵖ] Hᵐᵒᵖ := D.hermitian.scalarFunctional D.unit
abbrev remainder : V →ₗ[Hᵐᵒᵖ] D.kernel := D.hermitian.unitRemainder D.diagonal D.unit D.unit_norm

theorem scalar_unit : D.scalar D.unit = 1 := D.hermitian.scalarFunctional_self D.diagonal D.unit D.unit_norm

theorem reconstruct (x : V) : D.scalar x • D.unit + (D.remainder x : V) = x :=
  D.hermitian.unit_reconstruct D.diagonal D.unit D.unit_norm x

theorem norm_split (x : V) : ‖x‖ ^ 2 = ‖D.scalar x‖ ^ 2 + ‖D.remainder x‖ ^ 2 :=
  D.hermitian.unit_norm_split D.diagonal D.unit D.unit_norm x

theorem kernel_hasHermitianSquare : HasHermitianSquare (norm : D.kernel → ℝ) := by
  refine ⟨D.hermitian.comap D.kernel.subtype, ?_, ?_⟩
  · intro x
    exact D.diagonal x.val
  · intro x hx
    change 0 < (D.hermitian.form x.val x.val).re
    rw [D.diagonal, Quaternion.re_coe]
    change 0 < ‖x‖ ^ 2
    exact sq_pos_iff.mpr (norm_ne_zero_iff.mpr hx)

theorem kernel_finrank_add_one [FiniteDimensional Hᵐᵒᵖ V] :
    Module.finrank Hᵐᵒᵖ D.kernel + 1 = Module.finrank Hᵐᵒᵖ V :=
  D.hermitian.unitKernel_finrank_add_one D.diagonal D.unit D.unit_norm

def extensionLinearMap (g : D.kernel →ₗ[Hᵐᵒᵖ] E.kernel) : V →ₗ[Hᵐᵒᵖ] W :=
  (LinearMap.toSpanSingleton Hᵐᵒᵖ W E.unit).comp D.scalar +
    E.kernel.subtype.comp (g.comp D.remainder)

theorem extension_scalar (g : D.kernel →ₗ[Hᵐᵒᵖ] E.kernel) (x : V) :
    E.scalar (D.extensionLinearMap E g x) = D.scalar x := by
  change E.scalar (D.scalar x • E.unit + (g (D.remainder x) : W)) = D.scalar x
  rw [map_add, map_smul, E.scalar_unit,
    show E.scalar (g (D.remainder x) : W) = 0 from (g (D.remainder x)).property,
    smul_eq_mul, mul_one, add_zero]

theorem extension_remainder (g : D.kernel →ₗ[Hᵐᵒᵖ] E.kernel) (x : V) :
    E.remainder (D.extensionLinearMap E g x) = g (D.remainder x) := by
  apply Subtype.ext
  change D.extensionLinearMap E g x - E.scalar (D.extensionLinearMap E g x) • E.unit =
    (g (D.remainder x) : W)
  rw [D.extension_scalar E g x]
  change (D.scalar x • E.unit + (g (D.remainder x) : W)) - D.scalar x • E.unit = _
  abel

theorem extension_leftInverse (g : D.kernel ≃ₗ[Hᵐᵒᵖ] E.kernel) :
    Function.LeftInverse (E.extensionLinearMap D g.symm.toLinearMap)
      (D.extensionLinearMap E g.toLinearMap) := by
  intro x
  change E.scalar (D.extensionLinearMap E g.toLinearMap x) • D.unit +
    (g.symm (E.remainder (D.extensionLinearMap E g.toLinearMap x)) : V) = x
  rw [D.extension_scalar, D.extension_remainder]
  change D.scalar x • D.unit + (g.symm (g (D.remainder x)) : V) = x
  rw [g.symm_apply_apply]
  exact D.reconstruct x

def extensionEquiv (g : D.kernel ≃ₗ[Hᵐᵒᵖ] E.kernel) : V ≃ₗ[Hᵐᵒᵖ] W :=
  LinearEquiv.ofBijective (D.extensionLinearMap E g.toLinearMap)
    ⟨(D.extension_leftInverse E g).injective, (E.extension_leftInverse D g.symm).surjective⟩

def extensionIsometry (g : D.kernel ≃ₗᵢ[Hᵐᵒᵖ] E.kernel) : V ≃ₗᵢ[Hᵐᵒᵖ] W :=
  { D.extensionEquiv E g.toLinearEquiv with
    norm_map' := by
      intro x
      have hx := E.norm_split (D.extensionLinearMap E g.toLinearEquiv.toLinearMap x)
      rw [D.extension_scalar, D.extension_remainder] at hx
      change ‖D.extensionLinearMap E g.toLinearEquiv.toLinearMap x‖ ^ 2 =
        ‖D.scalar x‖ ^ 2 + ‖g (D.remainder x)‖ ^ 2 at hx
      rw [g.norm_map] at hx
      have hy := D.norm_split x
      change ‖D.extensionLinearMap E g.toLinearEquiv.toLinearMap x‖ = ‖x‖
      nlinarith [norm_nonneg (D.extensionLinearMap E g.toLinearEquiv.toLinearMap x), norm_nonneg x] }

end UnitHermitianData

theorem nonempty_unitHermitianData {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V]
    [NormSMulClass Hᵐᵒᵖ V] [Nontrivial V] (hV : HasHermitianSquare (norm : V → ℝ)) :
    Nonempty (UnitHermitianData V) := by
  obtain ⟨h, hdiag, _⟩ := hV
  obtain ⟨u, hu⟩ := exists_unit_vector (V := V)
  exact ⟨⟨h, hdiag, u, hu⟩⟩

end
end BanachIsometric.Quaternionic
