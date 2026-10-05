import Posets.WolfePreservationBlockJointPhaseKernel

/-! Exact coefficients for the fixed-phase kernel and its source marginal.
The large real diagonal estimate is transported to the actual adjoint
operator; no positivity or identity marginal is silently added. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

theorem wolfeJointPhaseKernel_coordinate
    (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) (y : K) (x : L) :
    wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y x =
      wolfeAtomicCrossRow N S y x * f (y, x) := by
  let g := (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L))
    (((JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K × L)).symm f).curry y)
  have he : (JLMS.evaluation (𝕜 := 𝕜) y).comp (wolfeJointPhaseKernel S f) =
      ((JLMS.evaluation y).comp S).comp (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 L) g) := by
    ext a
    exact wolfeJointPhaseKernel_slice S f a y
  unfold wolfeAtomicCrossRow
  rw [he, wolfeAtomicCoordinate_multiply]
  rfl

theorem wolfeJointPhaseKernel_marginal_coordinate
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (f : JLMS.CZero 𝕜 (K × L)) (x : L) :
    N.representation ((WeakDual.toStrongDual μ).comp (wolfeJointPhaseKernel S f)) x =
      JLMS.atomicRestriction P (univ ×ˢ {x}) (WeakDual.toStrongDual (wolfeJointLift S μ)) f := by
  classical
  let ν := WeakDual.toStrongDual (wolfeJointLift S μ)
  let a := M.representation (WeakDual.toStrongDual μ)
  let b := wolfeAtomicCrossRow N S
  have hs := JLMS.atomicDual_apply_hasSum P (JLMS.atomicRestriction P (univ ×ˢ {x}) ν) f
  rw [← hs.tsum_eq, hs.summable.tsum_prod]
  have he (y : K) : (∑' z : L,
      P.representation (JLMS.atomicRestriction P (univ ×ˢ {x}) ν) (y, z) * f (y, z)) =
      a y * b y x * f (y, x) := by
    rw [tsum_eq_single x]
    · rw [JLMS.atomicRestriction_coordinates]
      change JLMS.restrictionL1 (univ ×ˢ {x})
        (P.representation (WeakDual.toStrongDual (wolfeJointLift S μ))) (y, x) * f (y, x) = _
      rw [wolfeJointLift_coordinates M N P S μ]
      simp only [JLMS.restrictionL1_apply, JLMS.restrictL1_apply, mem_prod, mem_univ,
        mem_singleton_iff, and_self, if_true, wolfeJointCoefficients_apply]
      rfl
    · intro z hz
      rw [JLMS.atomicRestriction_coordinates]
      simp [JLMS.restrictionL1_apply, JLMS.restrictL1_apply, hz]
  simp_rw [he]
  have h := (wolfeAtomicCrossRow_pairing M N (wolfeJointPhaseKernel S f)
    (WeakDual.toStrongDual μ) x).tsum_eq
  simp only [wolfeJointPhaseKernel_coordinate, ← mul_assoc] at h
  exact h.symm

section Factorization
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeJointPhaseKernel_factorization_diagonal_lower
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (x : L) (f : JLMS.CZero 𝕜 (K × L)) (hf : ‖f‖ ≤ 1) :
    ‖c‖ - (wolfeJointVariation S (wolfeFactorizationLift T R c x) -
      RCLike.re (wolfeJointLift S (wolfeFactorizationLift T R c x) f)) ≤
      RCLike.re (N.representation ((WeakDual.toStrongDual (wolfeFactorizationLift T R c x)).comp
        (wolfeJointPhaseKernel S f)) x) := by
  rw [wolfeJointPhaseKernel_marginal_coordinate M N P]
  exact wolfeFactorizationJoint_phase_diagonal_lower M N P T R S hfactor c x f hf

end Factorization
end Posets
