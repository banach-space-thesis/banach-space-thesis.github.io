import Posets.WolfePreservationBlockJoint
import Mathlib.Topology.Semicontinuous

/-! The joint variation is the norm of an actual joint functional. It is
weak-star lower semicontinuous, uniformly bounded, and its source marginal
is the exact adjoint image. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

local instance wolfeBlockJointProductDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 (K × L) →L[𝕜] 𝕜) := inferInstance
local instance wolfeBlockJointProductDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 (K × L) →L[𝕜] 𝕜) := inferInstance

def wolfeJointSecondLinearMap : JLMS.CZero 𝕜 L →ₗ[𝕜] JLMS.CZero 𝕜 (K × L) where
  toFun f := (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K × L))
    ⟨fun z => f z.2, f.continuous.comp continuous_snd⟩
  map_add' f g := by ext z; rfl
  map_smul' r f := by ext z; rfl

theorem wolfeJointSecondLinearMap_bound (f : JLMS.CZero 𝕜 L) :
    ‖wolfeJointSecondLinearMap (K := K) f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro z
  exact JLMS.norm_CZero_apply_le f z.2

def wolfeJointSecondPullback : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 (K × L) :=
  (wolfeJointSecondLinearMap (𝕜 := 𝕜) (K := K) (L := L)).mkContinuous 1
    (wolfeJointSecondLinearMap_bound (𝕜 := 𝕜) (K := K) (L := L))

@[simp] theorem wolfeJointSecondPullback_apply (f : JLMS.CZero 𝕜 L) (y : K) (x : L) :
    wolfeJointSecondPullback f (y, x) = f x := rfl

theorem wolfeJointSecondPullback_norm_le :
    ‖wolfeJointSecondPullback (𝕜 := 𝕜) (K := K) (L := L)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) wolfeJointSecondLinearMap_bound

theorem wolfeJointOperator_second (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) :
    (wolfeJointCZeroOperator S).comp wolfeJointSecondPullback = S := by
  ext f y
  rw [ContinuousLinearMap.comp_apply, wolfeJointCZeroOperator_apply]
  congr 2

theorem wolfeJointLift_second (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    weakStarAdjoint wolfeJointSecondPullback (wolfeJointLift S μ) = weakStarAdjoint S μ := by
  apply DFunLike.ext
  intro f
  change μ ((wolfeJointCZeroOperator S) (wolfeJointSecondPullback f)) = μ (S f)
  rw [show (wolfeJointCZeroOperator S) (wolfeJointSecondPullback f) = S f from
    DFunLike.congr_fun (wolfeJointOperator_second S) f]

def wolfeJointVariation (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) : ℝ := ‖WeakDual.toStrongDual (wolfeJointLift S μ)‖

theorem wolfeJointVariation_nonneg (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) : 0 ≤ wolfeJointVariation S μ := by
  exact norm_nonneg (WeakDual.toStrongDual (wolfeJointLift S μ))

theorem wolfeJointVariation_le (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    wolfeJointVariation S μ ≤ ‖WeakDual.toStrongDual μ‖ * ‖S‖ := wolfeJointLift_norm_le S μ

theorem wolfeJointVariation_isClosed_sublevel (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (r : ℝ) : IsClosed {μ | wolfeJointVariation S μ ≤ r} := by
  have h := (WeakDual.isClosed_closedBall
    (0 : StrongDual 𝕜 (JLMS.CZero 𝕜 (K × L))) r).preimage (wolfeJointLift_continuous S)
  simpa only [wolfeJointVariation, Set.preimage, Metric.mem_closedBall, dist_zero_right] using h

theorem wolfeJointVariation_lowerSemicontinuous
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) : LowerSemicontinuous (wolfeJointVariation S) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  exact wolfeJointVariation_isClosed_sublevel S

section Factorization
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationJoint_second
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (x : L) :
    weakStarAdjoint wolfeJointSecondPullback
      (wolfeJointLift S (wolfeFactorizationLift T R c x)) = c • wolfeDirac x := by
  rw [wolfeJointLift_second]
  exact wolfeFactorizationLift_pullback T R S hfactor c x

theorem wolfeFactorizationJoint_norm_le
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (c : 𝕜) (hn : ‖c‖ * ‖R‖ ≤ 1) (x : L) :
    wolfeJointVariation S (wolfeFactorizationLift T R c x) ≤ ‖T‖ * ‖S‖ :=
  (wolfeJointVariation_le S _).trans (mul_le_mul_of_nonneg_right
    (wolfeFactorizationLift_norm_le T R c hn x) (norm_nonneg S))

end Factorization
end Posets
