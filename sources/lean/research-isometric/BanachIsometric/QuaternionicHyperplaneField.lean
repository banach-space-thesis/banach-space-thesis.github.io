import BanachIsometric.QuaternionicEuclidean
import BanachIsometric.HyperplanePairCoverage
import BanachIsometric.ExactSectionBundleConstruction

/-! Actual right quaternionic Hermitian hyperplanes with the original
real Euclidean norm. No noncommutative inner-product typeclass is introduced. -/

namespace BanachIsometric.Quaternionic

open Set MeasureTheory
open scoped Quaternion NNReal

noncomputable section

def standardHermitian (m : ℕ) : HermitianForm (Euclidean m) where
  form x y := ∑ r, star (x r) * y r
  add_right x y z := by simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  mul_right x y a := by
    change (∑ r, star (x r) * (y r * a)) = (∑ r, star (x r) * y r) * a
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)
  star_symm x y := by simp only [star_sum, star_mul, star_star]

theorem standardHermitian_re (m : ℕ) (x y : Euclidean m) :
    ((standardHermitian m).form x y).re = inner ℝ x y := by
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (∑ r, star (x r) * y r) =
    ∑ r, inner ℝ (x r) (y r)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  change (star (x r) * y r).re = inner ℝ (x r) (y r)
  rw [Quaternion.inner_def]
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

theorem standardHermitian_self (m : ℕ) (x : Euclidean m) :
    (standardHermitian m).form x x = (‖x‖ ^ 2 : ℝ) := by
  rw [(standardHermitian m).self_eq_re, standardHermitian_re, real_inner_self_eq_norm_sq]

def standardFunctional (m : ℕ) (u : Euclidean m) : Euclidean m →ₗ[Hᵐᵒᵖ] Hᵐᵒᵖ where
  toFun v := MulOpposite.op ((standardHermitian m).form u v)
  map_add' v w := by rw [(standardHermitian m).add_right, MulOpposite.op_add]
  map_smul' a v := by
    change MulOpposite.op ((standardHermitian m).form u (rightMul v a.unop)) =
      a * MulOpposite.op ((standardHermitian m).form u v)
    rw [(standardHermitian m).mul_right]
    rfl

def scalarNormalHyperplane (m : ℕ) (u : Euclidean m) : Submodule Hᵐᵒᵖ (Euclidean m) :=
  LinearMap.ker (standardFunctional m u)

abbrev realNormalHyperplane (m : ℕ) (u : Euclidean m) : Submodule ℝ (Euclidean m) :=
  (scalarNormalHyperplane m u).restrictScalars ℝ

@[simp] theorem mem_realNormalHyperplane (m : ℕ) (u v : Euclidean m) :
    v ∈ realNormalHyperplane m u ↔ (standardHermitian m).form u v = 0 := by
  change MulOpposite.op ((standardHermitian m).form u v) = MulOpposite.op (0 : H) ↔ _
  exact MulOpposite.op_injective.eq_iff

def normalProjection (m : ℕ) (u : Euclidean m) : Euclidean m →L[ℝ] Euclidean m :=
  ContinuousLinearMap.id ℝ _ -
    ((LinearMap.toSpanSingleton Hᵐᵒᵖ (Euclidean m) u).restrictScalars ℝ).toContinuousLinearMap.comp
      ((standardFunctional m u).restrictScalars ℝ).toContinuousLinearMap

@[simp] theorem normalProjection_apply (m : ℕ) (u v : Euclidean m) :
    normalProjection m u v = v - rightMul u ((standardHermitian m).form u v) := rfl

theorem realNormalHyperplane_le_perp (m : ℕ) (u : Euclidean m) :
    realNormalHyperplane m u ≤ (ℝ ∙ u)ᗮ := by
  intro v hv
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [← standardHermitian_re, (mem_realNormalHyperplane m u v).mp hv]
  rfl

theorem normalProjection_eq_starProjection (m : ℕ) (u : Euclidean m) (hu : ‖u‖ = 1) :
    normalProjection m u = (realNormalHyperplane m u).starProjection := by
  have huu : (standardHermitian m).form u u = 1 := by rw [standardHermitian_self, hu]; norm_num
  apply ContinuousLinearMap.ext
  intro v
  symm
  apply (realNormalHyperplane m u).eq_starProjection_of_mem_of_inner_eq_zero
  · change standardFunctional m u (v - rightMul u ((standardHermitian m).form u v)) = 0
    change standardFunctional m u (v - MulOpposite.op ((standardHermitian m).form u v) • u) = 0
    rw [map_sub, map_smul]
    change MulOpposite.op ((standardHermitian m).form u v) -
      MulOpposite.op ((standardHermitian m).form u v) * MulOpposite.op ((standardHermitian m).form u u) = 0
    rw [huu, MulOpposite.op_one, mul_one, sub_self]
  · intro w hw
    have hd : v - normalProjection m u v = rightMul u ((standardHermitian m).form u v) := by
      rw [normalProjection_apply]
      abel
    rw [hd, ← standardHermitian_re, (standardHermitian m).mul_left,
      (mem_realNormalHyperplane m u w).mp hw, mul_zero]
    rfl

theorem scalarNormalHyperplane_finrank (n : ℕ) (u : Euclidean (n + 1)) (hu : ‖u‖ = 1) :
    Module.finrank Hᵐᵒᵖ (scalarNormalHyperplane (n + 1) u) = n := by
  have huu : standardFunctional (n + 1) u u = 1 := by
    change MulOpposite.op ((standardHermitian (n + 1)).form u u) = 1
    rw [standardHermitian_self, hu]
    norm_num
  have hne : standardFunctional (n + 1) u ≠ 0 := by
    intro h
    have hh := congrArg (fun f : Euclidean (n + 1) →ₗ[Hᵐᵒᵖ] Hᵐᵒᵖ => f u) h
    change standardFunctional (n + 1) u u = 0 at hh
    rw [huu] at hh
    exact one_ne_zero hh
  have hdim := (standardFunctional (n + 1) u).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (nonzero_functional_surjective hne),
    finrank_top, Module.finrank_self, finrank_right_euclidean] at hdim
  change 1 + Module.finrank Hᵐᵒᵖ (scalarNormalHyperplane (n + 1) u) = n + 1 at hdim
  omega

theorem realNormalHyperplane_finrank (n : ℕ) (u : Euclidean (n + 1)) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (realNormalHyperplane (n + 1) u) = 4 * n := by
  have heq : Module.finrank Hᵐᵒᵖ (realNormalHyperplane (n + 1) u) = n :=
    ((scalarNormalHyperplane (n + 1) u).restrictScalarsEquiv ℝ).finrank_eq.trans
      (scalarNormalHyperplane_finrank n u hu)
  have h := Module.finrank_mul_finrank ℝ Hᵐᵒᵖ (realNormalHyperplane (n + 1) u)
  rw [finrank_real_opposite, heq] at h
  exact h.symm

end
end BanachIsometric.Quaternionic
