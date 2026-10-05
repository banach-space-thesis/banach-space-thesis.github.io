import Posets.WolfePreservationBlockRegions
import JLMS.CompactCZeroEquiv

/-! The joint kernel of an operator between compact continuous-function
spaces. Its adjoint retains both the input point and the source measure,
instead of discarding their continuous dependence in an atomic selection. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

def wolfeJointContinuous (S : C(L, 𝕜) →L[𝕜] C(K, 𝕜))
    (f : C(K × L, 𝕜)) : C(K, 𝕜) :=
  ⟨fun y => S (f.curry y) y,
    continuous_eval.comp ((S.continuous.comp f.curry.continuous).prodMk continuous_id)⟩

@[simp] theorem wolfeJointContinuous_apply (S : C(L, 𝕜) →L[𝕜] C(K, 𝕜))
    (f : C(K × L, 𝕜)) (y : K) : wolfeJointContinuous S f y = S (f.curry y) y := rfl

def wolfeJointLinearMap (S : C(L, 𝕜) →L[𝕜] C(K, 𝕜)) :
    C(K × L, 𝕜) →ₗ[𝕜] C(K, 𝕜) where
  toFun := wolfeJointContinuous S
  map_add' f g := by
    ext y
    change S ((f + g).curry y) y = S (f.curry y) y + S (g.curry y) y
    have he : (f + g).curry y = f.curry y + g.curry y := by ext x; rfl
    rw [he, map_add]
    rfl
  map_smul' r f := by
    ext y
    change S ((r • f).curry y) y = (r • S (f.curry y)) y
    have he : (r • f).curry y = r • f.curry y := by ext x; rfl
    rw [he, map_smul]

theorem wolfeJointLinearMap_bound (S : C(L, 𝕜) →L[𝕜] C(K, 𝕜))
    (f : C(K × L, 𝕜)) : ‖wolfeJointLinearMap S f‖ ≤ ‖S‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg S) (norm_nonneg f))).mpr
  intro y
  have hf : ‖f.curry y‖ ≤ ‖f‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    exact f.norm_coe_le_norm (y, x)
  exact ((S (f.curry y)).norm_coe_le_norm y).trans
    ((S.le_opNorm _).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg S)))

def wolfeJointOperator (S : C(L, 𝕜) →L[𝕜] C(K, 𝕜)) :
    C(K × L, 𝕜) →L[𝕜] C(K, 𝕜) :=
  (wolfeJointLinearMap S).mkContinuous ‖S‖ (wolfeJointLinearMap_bound S)

theorem wolfeJointOperator_norm_le (S : C(L, 𝕜) →L[𝕜] C(K, 𝕜)) :
    ‖wolfeJointOperator S‖ ≤ ‖S‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) (wolfeJointLinearMap_bound S)

def wolfeJointCZeroOperator (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) :
    JLMS.CZero 𝕜 (K × L) →L[𝕜] JLMS.CZero 𝕜 K :=
  let eK := (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K)).toContinuousLinearEquiv
  let eL := (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L)).toContinuousLinearEquiv
  let eKL := (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K × L)).toContinuousLinearEquiv
  eK.toContinuousLinearMap.comp ((wolfeJointOperator
    (eK.symm.toContinuousLinearMap.comp (S.comp eL.toContinuousLinearMap))).comp
      eKL.symm.toContinuousLinearMap)

theorem wolfeJointCZeroOperator_apply (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) (y : K) :
    wolfeJointCZeroOperator S f y = S ((JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L))
      (((JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K × L)).symm f).curry y)) y := rfl

theorem wolfeJointCZeroOperator_bound (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) : ‖wolfeJointCZeroOperator S f‖ ≤ ‖S‖ * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg S) (norm_nonneg f))).mpr
  intro y
  change ‖wolfeJointCZeroOperator S f y‖ ≤ _
  rw [wolfeJointCZeroOperator_apply]
  apply (JLMS.norm_CZero_apply_le _ y).trans
  apply (S.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg S)
  rw [JLMS.compactContinuousCZeroEquiv.norm_map]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact JLMS.norm_CZero_apply_le f (y, x)

theorem wolfeJointCZeroOperator_norm_le (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) :
    ‖wolfeJointCZeroOperator S‖ ≤ ‖S‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) (wolfeJointCZeroOperator_bound S)

def wolfeJointLift (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) :
    WeakDual 𝕜 (JLMS.CZero 𝕜 K) → WeakDual 𝕜 (JLMS.CZero 𝕜 (K × L)) :=
  weakStarAdjoint (wolfeJointCZeroOperator S)

theorem wolfeJointLift_continuous (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) :
    Continuous (wolfeJointLift S) := weakStarAdjoint_continuous _

theorem wolfeJointLift_norm_le (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    ‖WeakDual.toStrongDual (wolfeJointLift S μ)‖ ≤ ‖WeakDual.toStrongDual μ‖ * ‖S‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (wolfeJointCZeroOperator_norm_le S) (norm_nonneg _))

end Posets
