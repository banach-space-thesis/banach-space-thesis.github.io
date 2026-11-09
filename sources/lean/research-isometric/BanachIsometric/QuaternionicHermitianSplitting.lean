import BanachIsometric.QuaternionicCompletion
import BanachIsometric.HyperplanePairCoverage

/-! Splitting a genuine quaternionic Hermitian norm space into a unit right
line and its scalar orthogonal kernel. These are algebraic right-linear
coordinates with an exact norm-square identity, without a quaternionic
inner-product typeclass or a replacement norm. -/

namespace BanachIsometric.Quaternionic

open scoped Quaternion

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V]

theorem exists_unit_vector [NormSMulClass Hᵐᵒᵖ V] [Nontrivial V] : ∃ u : V, ‖u‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨rightMul v ((‖v‖⁻¹ : ℝ) : H), ?_⟩
  change ‖MulOpposite.op ((‖v‖⁻¹ : ℝ) : H) • v‖ = 1
  rw [norm_smul, MulOpposite.norm_op, Quaternion.norm_coe,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

def HermitianForm.scalarFunctional (h : HermitianForm V) (u : V) : V →ₗ[Hᵐᵒᵖ] Hᵐᵒᵖ where
  toFun v := MulOpposite.op (h.form u v)
  map_add' v w := by rw [h.add_right, MulOpposite.op_add]
  map_smul' a v := by
    change MulOpposite.op (h.form u (rightMul v a.unop)) = a * MulOpposite.op (h.form u v)
    rw [h.mul_right]
    rfl

def HermitianForm.unitKernel (h : HermitianForm V) (u : V) : Submodule Hᵐᵒᵖ V :=
  LinearMap.ker (h.scalarFunctional u)

theorem HermitianForm.scalarFunctional_self (h : HermitianForm V)
    (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) (u : V) (hu : ‖u‖ = 1) :
    h.scalarFunctional u u = 1 := by
  change MulOpposite.op (h.form u u) = 1
  rw [hdiag, hu]
  norm_num

def HermitianForm.unitRemainder (h : HermitianForm V)
    (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) (u : V) (hu : ‖u‖ = 1) :
    V →ₗ[Hᵐᵒᵖ] h.unitKernel u :=
  (LinearMap.id - (LinearMap.toSpanSingleton Hᵐᵒᵖ V u).comp (h.scalarFunctional u)).codRestrict _ (by
    intro v
    change h.scalarFunctional u (v - h.scalarFunctional u v • u) = 0
    rw [map_sub, map_smul, h.scalarFunctional_self hdiag u hu, smul_eq_mul, mul_one, sub_self])

@[simp] theorem HermitianForm.unitRemainder_coe (h : HermitianForm V)
    (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) (u : V) (hu : ‖u‖ = 1) (v : V) :
    (h.unitRemainder hdiag u hu v : V) = v - h.scalarFunctional u v • u := rfl

theorem HermitianForm.unit_reconstruct (h : HermitianForm V)
    (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) (u : V) (hu : ‖u‖ = 1) (v : V) :
    h.scalarFunctional u v • u + (h.unitRemainder hdiag u hu v : V) = v := by
  rw [h.unitRemainder_coe]
  abel

theorem HermitianForm.unitKernel_form_eq_zero (h : HermitianForm V) (u : V) (z : h.unitKernel u) :
    h.form u z.val = 0 := by
  apply MulOpposite.op_injective
  exact z.property

theorem HermitianForm.unitRemainder_of_kernel (h : HermitianForm V)
    (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) (u : V) (hu : ‖u‖ = 1) (z : h.unitKernel u) :
    h.unitRemainder hdiag u hu z.val = z := by
  apply Subtype.ext
  change z.val - h.scalarFunctional u z.val • u = z.val
  rw [show h.scalarFunctional u z.val = 0 from z.property, zero_smul, sub_zero]

theorem HermitianForm.unit_norm_split (h : HermitianForm V)
    (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) (u : V) (hu : ‖u‖ = 1) (v : V) :
    ‖v‖ ^ 2 = ‖h.scalarFunctional u v‖ ^ 2 + ‖h.unitRemainder hdiag u hu v‖ ^ 2 := by
  let a := (h.scalarFunctional u v).unop
  let z := h.unitRemainder hdiag u hu v
  have huv : h.form u z.val = 0 := h.unitKernel_form_eq_zero u z
  have hzu : h.form z.val u = 0 := by rw [← h.star_symm u z.val, huv, star_zero]
  have huu : h.form u u = 1 := by rw [hdiag, hu]; norm_num
  have hrecon : rightMul u a + z.val = v := h.unit_reconstruct hdiag u hu v
  have hsplit : h.form (rightMul u a + z.val) (rightMul u a + z.val) =
      star a * a + (‖z.val‖ ^ 2 : ℝ) := by
    simp only [h.add_left, h.add_right, h.mul_left, h.mul_right, huv, hzu, huu, hdiag z.val,
      mul_zero, zero_mul, one_mul, add_zero, zero_add]
  have hr := congrArg QuaternionAlgebra.re hsplit
  rw [hrecon, hdiag, Quaternion.re_add, Quaternion.star_mul_self, Quaternion.re_coe,
    Quaternion.re_coe, Quaternion.normSq_eq_norm_mul_self] at hr
  change ‖v‖ ^ 2 = ‖a‖ * ‖a‖ + ‖z.val‖ ^ 2 at hr
  change ‖v‖ ^ 2 = ‖a‖ ^ 2 + ‖z.val‖ ^ 2
  nlinarith [hr]

theorem HermitianForm.unitKernel_finrank_add_one [FiniteDimensional Hᵐᵒᵖ V]
    (h : HermitianForm V) (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) (u : V) (hu : ‖u‖ = 1) :
    Module.finrank Hᵐᵒᵖ (h.unitKernel u) + 1 = Module.finrank Hᵐᵒᵖ V := by
  have hne : h.scalarFunctional u ≠ 0 := by
    intro hz
    have he := DFunLike.congr_fun hz u
    rw [h.scalarFunctional_self hdiag u hu] at he
    exact one_ne_zero he
  have hdim := (h.scalarFunctional u).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (nonzero_functional_surjective hne), finrank_top, Module.finrank_self] at hdim
  change 1 + Module.finrank Hᵐᵒᵖ (h.unitKernel u) = Module.finrank Hᵐᵒᵖ V at hdim
  omega

end
end BanachIsometric.Quaternionic
