import BanachIsometric.QuaternionicStatements
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Quaternionic reduction from Theorem A to Corollary B

The existing norm and right quaternionic action are retained. Real normed-space
structures are installed only on restriction-of-scalars type aliases, so
Mazur--Ulam and finite-dimensional Lipschitz regularity apply without pretending
that quaternions are a commutative normed field. Theorem A remains an explicit
premise in the final implication.
-/

namespace BanachIsometric
namespace Quaternionic

open scoped Quaternion NNReal

attribute [local instance] RestrictScalars.moduleOrig

theorem finrank_real_quaternion_op : Module.finrank ℝ Hᵐᵒᵖ = 4 := by
  let e : H ≃ₗ[ℝ] Hᵐᵒᵖ := MulOpposite.opLinearEquiv ℝ
  rw [← e.finrank_eq]
  exact Quaternion.finrank_eq_four

/-- The underlying real dimension is four times the right quaternionic
dimension. This numerical identity is used only with established finiteness
in the sphere-regularity argument below. -/
theorem finrank_real_restrict (E : Type*) [AddCommGroup E] [Module Hᵐᵒᵖ E] :
    Module.finrank ℝ (RestrictScalars ℝ Hᵐᵒᵖ E) = 4 * Module.finrank Hᵐᵒᵖ E := by
  have h := Module.finrank_mul_finrank ℝ Hᵐᵒᵖ (RestrictScalars ℝ Hᵐᵒᵖ E)
  rw [finrank_real_quaternion_op] at h
  exact h.symm

variable {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]

/-- Restrict the original norm-compatible right action to real scalars,
without changing the norm or the original right action. -/
noncomputable def realNormedSpace : NormedSpace ℝ (RestrictScalars ℝ Hᵐᵒᵖ V) := by
  letI : NormSMulClass Hᵐᵒᵖ (RestrictScalars ℝ Hᵐᵒᵖ V) :=
    (inferInstance : NormSMulClass Hᵐᵒᵖ V)
  exact { RestrictScalars.module ℝ Hᵐᵒᵖ V with
    norm_smul_le := fun r x => by
      change ‖(MulOpposite.op (r : H)) • (x : V)‖ ≤ ‖r‖ * ‖(x : V)‖
      rw [norm_smul]
      change ‖(r : H)‖ * ‖x‖ ≤ ‖r‖ * ‖x‖
      rw [Quaternion.norm_coe] }

/-- The inherited subspace norm is compatible with exactly the original
right quaternionic scalar action. -/
def submoduleNormSMul (Y : Submodule Hᵐᵒᵖ V) : NormSMulClass Hᵐᵒᵖ Y where
  norm_smul a y := norm_smul (β := V) a y.val

/-- A norm has the local sphere Lipschitz regularity in the exact real
coordinates appearing in the quaternionic functional target. -/
theorem norm_sphereLipschitz (n : ℕ) : SphereLipschitz n (norm : V → ℝ) := by
  intro Y hY
  letI : Module.Finite Hᵐᵒᵖ Y := Module.finite_of_rank_eq_nat hY
  letI : Module.Finite Hᵐᵒᵖ (RestrictScalars ℝ Hᵐᵒᵖ Y) :=
    (inferInstance : Module.Finite Hᵐᵒᵖ Y)
  letI : Module.Finite ℝ (RestrictScalars ℝ Hᵐᵒᵖ Y) :=
    Module.Finite.trans Hᵐᵒᵖ (RestrictScalars ℝ Hᵐᵒᵖ Y)
  letI : NormSMulClass Hᵐᵒᵖ Y := submoduleNormSMul Y
  letI : NormedSpace ℝ (RestrictScalars ℝ Hᵐᵒᵖ Y) := realNormedSpace (V := Y)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 * (n + 1)))) =
      Module.finrank ℝ (RestrictScalars ℝ Hᵐᵒᵖ Y) := by
    rw [finrank_real_restrict, Module.finrank_eq_of_rank_eq hY]
    simp
  let e := LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin (4 * (n + 1))))
    (RestrictScalars ℝ Hᵐᵒᵖ Y) hdim
  let f : EuclideanSpace ℝ (Fin (4 * (n + 1))) →L[ℝ]
      RestrictScalars ℝ Hᵐᵒᵖ Y := LinearMap.toContinuousLinearMap e.toLinearMap
  refine ⟨e, ‖f‖₊, ?_⟩
  have hf : LipschitzWith ‖f‖₊ f := f.lipschitz
  simpa [f, Function.comp_def, RestrictScalars.addEquiv] using
    (lipschitzWith_one_norm.comp hf).lipschitzOnWith

/-- Arbitrary bijective metric isometries give precisely the real-linear
norm-preserving section maps allowed by the paper, after centering by
Mazur--Ulam. The maps need not be quaternionic linear or fix zero initially. -/
theorem metricSubspaceHomogeneity_realEquivalentSections {n : ℕ}
    (h : MetricSubspaceHomogeneity (V := V) n) :
    RealEquivalentSections n (norm : V → ℝ) := by
  intro Y Z hY hZ
  obtain ⟨g⟩ := h Y Z hY hZ
  letI : NormSMulClass Hᵐᵒᵖ Y := submoduleNormSMul Y
  letI : NormSMulClass Hᵐᵒᵖ Z := submoduleNormSMul Z
  letI : NormedSpace ℝ (RestrictScalars ℝ Hᵐᵒᵖ Y) := realNormedSpace (V := Y)
  letI : NormedSpace ℝ (RestrictScalars ℝ Hᵐᵒᵖ Z) := realNormedSpace (V := Z)
  let e :=
    (show RestrictScalars ℝ Hᵐᵒᵖ Y ≃ᵢ RestrictScalars ℝ Hᵐᵒᵖ Z from g).toRealLinearIsometryEquiv
  refine ⟨e.toLinearEquiv, ?_⟩
  intro x
  exact e.norm_map x

/-- The quaternionic normed corollary follows from the functional theorem.
The functional theorem is an explicit argument, not an added axiom or a
proved geometric assertion in this file. The conclusion preserves the given
norm and original right quaternionic action. -/
theorem functionalStatement_implies_corollaryB (h : FunctionalStatement (E := V)) (n : ℕ) :
    NormedCorollaryBAt (V := V) n := by
  intro hn hdim hmetric
  exact h n norm hn hdim norm_isDefiniteHomogeneous (norm_sphereLipschitz n)
    (metricSubspaceHomogeneity_realEquivalentSections hmetric)

end Quaternionic
end BanachIsometric
