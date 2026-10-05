import Posets.WolfePreservationBlockJointPhaseCore

/-! The fixed joint phase defines an actual operator kernel. Its adjoint
source coordinates are the phase-modified diagonal fibres, rather than
the original exact identity marginal. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

def wolfeJointPhaseKernel (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K :=
  (wolfeJointCZeroOperator S).comp
    ((ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 (K × L)) f).comp wolfeJointSecondPullback)

@[simp] theorem wolfeJointPhaseKernel_apply
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) (g : JLMS.CZero 𝕜 L) :
    wolfeJointPhaseKernel S f g = wolfeJointCZeroOperator S (f * wolfeJointSecondPullback g) := rfl

theorem wolfeJointPhaseKernel_norm_le
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) : ‖wolfeJointPhaseKernel S f‖ ≤ ‖S‖ * ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg S) (norm_nonneg f))
  intro g
  rw [wolfeJointPhaseKernel_apply]
  apply (wolfeJointCZeroOperator_bound S _).trans
  calc
    ‖S‖ * ‖f * wolfeJointSecondPullback g‖ ≤
        ‖S‖ * (‖f‖ * ‖wolfeJointSecondPullback (K := K) g‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg S)
    _ ≤ ‖S‖ * (‖f‖ * ‖g‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using
        wolfeJointSecondLinearMap_bound (K := K) g) (norm_nonneg f)) (norm_nonneg S)
    _ = (‖S‖ * ‖f‖) * ‖g‖ := by ring

theorem wolfeJointPhaseKernel_slice
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) (g : JLMS.CZero 𝕜 L) (y : K) :
    wolfeJointPhaseKernel S f g y =
      S (((JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L))
        (((JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K × L)).symm f).curry y)) * g) y := by
  rw [wolfeJointPhaseKernel_apply, wolfeJointCZeroOperator_apply]
  congr 2

end Posets

namespace Posets
variable {𝕜 Y : Type*} [RCLike 𝕜] [TopologicalSpace Y]
local instance wolfePhaseMultiplierDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 Y →L[𝕜] 𝕜) := inferInstance
local instance wolfePhaseMultiplierDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 Y →L[𝕜] 𝕜) := inferInstance

theorem wolfeAtomicCoordinate_multiply (N : JLMS.AtomicDualModel 𝕜 Y)
    (φ : JLMS.CZero 𝕜 Y →L[𝕜] 𝕜) (g : JLMS.CZero 𝕜 Y) (x : Y) :
    N.representation (φ.comp (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 Y) g)) x =
      N.representation φ x * g x := by
  classical
  let A := (wolfeAtomicCoordinate N x).comp
    (JLMS.banachAdjoint (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 Y) g))
  have h := (JLMS.atomicDual_hasSum N φ).map A A.continuous
  have he (y : Y) : A (N.representation φ y • JLMS.evaluation y) =
      if y = x then N.representation φ x * g x else 0 := by
    have hmul : (JLMS.evaluation (𝕜 := 𝕜) y).comp
        (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 Y) g) = g y • JLMS.evaluation y := by
      ext a
      rfl
    have hpoint : N.representation (JLMS.evaluation (𝕜 := 𝕜) y) = lp.single 1 y (1 : 𝕜) := by
      rw [← N.pointMass y, N.representation.apply_symm_apply]
    change N.representation ((N.representation φ y • JLMS.evaluation y).comp
      (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 Y) g)) x = _
    rw [ContinuousLinearMap.smul_comp, hmul, map_smul, map_smul, hpoint]
    by_cases hy : y = x
    · subst y
      simp
    · simp [lp.single_apply, hy, Ne.symm hy]
  have ht : (∑' y, A (N.representation φ y • JLMS.evaluation y)) = A φ := h.tsum_eq
  simp only [he] at ht
  simpa using ht.symm

end Posets
