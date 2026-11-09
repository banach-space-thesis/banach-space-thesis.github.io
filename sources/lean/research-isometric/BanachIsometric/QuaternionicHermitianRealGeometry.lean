import BanachIsometric.QuaternionicEuclidean
import BanachIsometric.HermitianRelativeOperator
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The real geometry of the original right quaternionic Hermitian forms

The right action is the given `Module Hᵐᵒᵖ E`. Taking real parts gives an
actual real symmetric bilinear form. A given first Hermitian form compatible
with the existing real inner product supplies its actual normal hyperplanes
and orthogonal projections; no quaternionic inner-product typeclass is used.
-/

namespace BanachIsometric.Quaternionic

open scoped Quaternion NNReal

noncomputable section

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module Hᵐᵒᵖ E] [Module ℝ E]
  [IsScalarTower ℝ Hᵐᵒᵖ E]

def HermitianForm.realBilinear (h : HermitianForm E) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => (h.form x y).re
      map_add' y z := by rw [h.add_right, Quaternion.re_add]
      map_smul' r y := by
        rw [← rightMul_real y r, h.mul_right]
        simp only [Quaternion.re_mul, Quaternion.re_coe, Quaternion.imI_coe,
          Quaternion.imJ_coe, Quaternion.imK_coe, mul_zero, sub_zero, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' x y := by
    ext z
    exact congrArg QuaternionAlgebra.re (h.add_left x y z)
  map_smul' r x := by
    ext y
    change (h.form (r • x) y).re = r * (h.form x y).re
    rw [← rightMul_real x r, h.mul_left]
    simp only [Quaternion.star_coe, Quaternion.re_mul, Quaternion.re_coe,
      Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe, zero_mul, sub_zero]

@[simp]
theorem HermitianForm.realBilinear_apply (h : HermitianForm E) (x y : E) :
    h.realBilinear x y = (h.form x y).re := rfl

theorem HermitianForm.realBilinear_symmetric (h : HermitianForm E) (x y : E) :
    h.realBilinear x y = h.realBilinear y x := by
  change (h.form x y).re = (h.form y x).re
  rw [← h.star_symm, Quaternion.re_star]

omit [Module ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem HermitianForm.real_self_rightMul (h : HermitianForm E) (x : E) (a : H) :
    (h.form (rightMul x a) (rightMul x a)).re = Quaternion.normSq a * (h.form x x).re := by
  rw [h.mul_left, h.mul_right, h.self_eq_re x]
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_coe, Quaternion.imI_coe,
    Quaternion.imJ_coe, Quaternion.imK_coe, zero_mul, add_zero, sub_zero,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.normSq_def']
  ring

def hermitianNormalFunctional (P : HermitianForm E) (u : E) : E →ₗ[Hᵐᵒᵖ] Hᵐᵒᵖ where
  toFun v := MulOpposite.op (P.form u v)
  map_add' v w := by rw [P.add_right, MulOpposite.op_add]
  map_smul' a v := by
    change MulOpposite.op (P.form u (rightMul v a.unop)) = a * MulOpposite.op (P.form u v)
    rw [P.mul_right]
    rfl

def hermitianNormalHyperplane (P : HermitianForm E) (u : E) : Submodule Hᵐᵒᵖ E :=
  LinearMap.ker (hermitianNormalFunctional P u)

abbrev realHermitianNormalHyperplane (P : HermitianForm E) (u : E) : Submodule ℝ E :=
  (hermitianNormalHyperplane P u).restrictScalars ℝ

omit [Module ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E] in
@[simp]
theorem mem_hermitianNormalHyperplane (P : HermitianForm E) (u v : E) :
    v ∈ hermitianNormalHyperplane P u ↔ P.form u v = 0 := by
  change MulOpposite.op (P.form u v) = MulOpposite.op (0 : H) ↔ _
  exact MulOpposite.op_injective.eq_iff

@[simp]
theorem mem_realHermitianNormalHyperplane (P : HermitianForm E) (u v : E) :
    v ∈ realHermitianNormalHyperplane P u ↔ P.form u v = 0 :=
  mem_hermitianNormalHyperplane P u v

end Algebraic

section RealInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module Hᵐᵒᵖ E] [IsScalarTower ℝ Hᵐᵒᵖ E]
  (P : HermitianForm E) (hP : ∀ x y, (P.form x y).re = inner ℝ x y)

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
include hP in
theorem hermitian_self_eq_norm_sq (x : E) : P.form x x = (‖x‖ ^ 2 : ℝ) := by
  rw [P.self_eq_re, hP, real_inner_self_eq_norm_sq]

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
include hP in
theorem norm_sq_rightMul (x : E) (a : H) :
    ‖rightMul x a‖ ^ 2 = Quaternion.normSq a * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← hP, P.real_self_rightMul, hP,
    real_inner_self_eq_norm_sq]

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
include hP in
theorem unit_hermitian_self (u : E) (hu : ‖u‖ = 1) : P.form u u = 1 := by
  rw [hermitian_self_eq_norm_sq P hP, hu]
  norm_num

variable [FiniteDimensional Hᵐᵒᵖ E]

local instance : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ Hᵐᵒᵖ E

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
include hP in
theorem hermitianNormalHyperplane_finrank {n : ℕ}
    (hdim : Module.finrank Hᵐᵒᵖ E = n + 1) (u : E) (hu : ‖u‖ = 1) :
    Module.finrank Hᵐᵒᵖ (hermitianNormalHyperplane P u) = n := by
  have huu := unit_hermitian_self P hP u hu
  have hsurj : Function.Surjective (hermitianNormalFunctional P u) := by
    intro a
    refine ⟨rightMul u a.unop, ?_⟩
    change MulOpposite.op (P.form u (rightMul u a.unop)) = a
    rw [P.mul_right, huu, one_mul]
    exact MulOpposite.op_unop a
  have h := (hermitianNormalFunctional P u).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, hdim] at h
  change 1 + Module.finrank Hᵐᵒᵖ (hermitianNormalHyperplane P u) = n + 1 at h
  omega

include hP in
theorem realHermitianNormalHyperplane_finrank {n : ℕ}
    (hdim : Module.finrank Hᵐᵒᵖ E = n + 1) (u : E) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (realHermitianNormalHyperplane P u) = 4 * n := by
  have hd := hermitianNormalHyperplane_finrank P hP hdim u hu
  have heq : Module.finrank Hᵐᵒᵖ ((hermitianNormalHyperplane P u).restrictScalars ℝ) = n :=
    ((hermitianNormalHyperplane P u).restrictScalarsEquiv ℝ).finrank_eq.trans hd
  have h := Module.finrank_mul_finrank ℝ Hᵐᵒᵖ ((hermitianNormalHyperplane P u).restrictScalars ℝ)
  rw [finrank_real_opposite, heq] at h
  exact h.symm

def hermitianNormalPart (u : E) : E →L[ℝ] E :=
  ((LinearMap.toSpanSingleton Hᵐᵒᵖ E u).restrictScalars ℝ).toContinuousLinearMap.comp
    ((hermitianNormalFunctional P u).restrictScalars ℝ).toContinuousLinearMap

@[simp]
theorem hermitianNormalPart_apply (u v : E) :
    hermitianNormalPart P u v = rightMul u (P.form u v) := rfl

include hP in
theorem hermitianNormalProjection_eq_starProjection (u : E) (hu : ‖u‖ = 1) :
    ContinuousLinearMap.id ℝ E - hermitianNormalPart P u =
      (realHermitianNormalHyperplane P u).starProjection := by
  ext v
  symm
  apply (realHermitianNormalHyperplane P u).eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_realHermitianNormalHyperplane]
    change P.form u (v - rightMul u (P.form u v)) = 0
    have hs := (hermitianNormalFunctional P u).map_sub v (rightMul u (P.form u v))
    change MulOpposite.op (P.form u (v - rightMul u (P.form u v))) = _ at hs
    apply MulOpposite.op_injective
    rw [hs]
    change MulOpposite.op (P.form u v) - MulOpposite.op (P.form u (rightMul u (P.form u v))) = 0
    rw [P.mul_right, unit_hermitian_self P hP u hu, one_mul, sub_self]
  · intro w hw
    have hd : v - ((ContinuousLinearMap.id ℝ E - hermitianNormalPart P u) v) =
        rightMul u (P.form u v) := by
      change v - (v - rightMul u (P.form u v)) = _
      abel
    rw [hd, ← hP, P.mul_left, (mem_realHermitianNormalHyperplane P u w).mp hw, mul_zero]
    rfl

end RealInner

end

end BanachIsometric.Quaternionic
