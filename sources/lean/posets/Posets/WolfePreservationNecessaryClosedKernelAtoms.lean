import Posets.WolfePreservationNecessaryClosedKernel
import Posets.WolfePreservationBlockJointPhase

/-! A uniform positivity defect turns large atomic coefficients into the
closed clopen-test relation. Normalized rows of norm at most 1 + τ have exactly
the required defect bound. No continuity of atomic coordinates is used. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace L] [CompactSpace L]

local instance wolfeClosedKernelAtomsDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance
local instance wolfeClosedKernelAtomsDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance

theorem wolfeSourceBlock_restriction_one (N : JLMS.AtomicDualModel 𝕜 L)
    (φ : JLMS.CZero 𝕜 L →L[𝕜] 𝕜) (V : Set L) (hV : IsClopen V) :
    JLMS.atomicRestriction N V φ (wolfeSourceBlock univ isClopen_univ) =
      φ (wolfeSourceBlock V hV) := by
  classical
  apply (JLMS.atomicDual_apply_hasSum N (JLMS.atomicRestriction N V φ)
    (wolfeSourceBlock univ isClopen_univ)).unique
  apply (JLMS.atomicDual_apply_hasSum N φ (wolfeSourceBlock V hV)).congr_fun
  intro x
  simp only [JLMS.atomicRestriction_coordinates, wolfeSourceBlock_apply,
    mem_univ, if_true, mul_one, JLMS.restrictionL1_apply, JLMS.restrictL1_apply]
  split_ifs <;> simp

theorem wolfeClopenKernelRelation_mem_of_atom
    (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (y : K) (x : L) {d τ : ℝ}
    (hdefect : ‖WeakDual.toStrongDual (ν y)‖ -
      RCLike.re (ν y (wolfeSourceBlock univ isClopen_univ)) ≤ τ)
    (hatom : d + τ ≤ ‖N.representation (WeakDual.toStrongDual (ν y)) x‖) :
    (y, x) ∈ wolfeClopenKernelRelation ν d := by
  intro V hV hx
  have hphase := wolfePhaseRestriction_re_lower N (ν y)
    (wolfeSourceBlock univ isClopen_univ)
    (wolfeSourceBlock_norm_le univ isClopen_univ) V
  rw [wolfeSourceBlock_restriction_one N _ V hV] at hphase
  have hmass : ‖N.representation (WeakDual.toStrongDual (ν y)) x‖ ≤ wolfeMass N (ν y) V := by
    rw [← wolfeMass_singleton]
    exact wolfeMass_mono N (ν y) (singleton_subset_iff.mpr hx)
  change wolfeMass N (ν y) V - (‖WeakDual.toStrongDual (ν y)‖ -
    RCLike.re (ν y (wolfeSourceBlock univ isClopen_univ))) ≤
      RCLike.re (ν y (wolfeSourceBlock V hV)) at hphase
  change d ≤ RCLike.re (ν y (wolfeSourceBlock V hV))
  linarith

theorem wolfeClopenKernelRelation_mem_of_normalized_atom
    (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (y : K) (x : L) {d τ : ℝ}
    (hone : ν y (wolfeSourceBlock univ isClopen_univ) = 1)
    (hnorm : ‖WeakDual.toStrongDual (ν y)‖ ≤ 1 + τ)
    (hatom : d + τ ≤ ‖N.representation (WeakDual.toStrongDual (ν y)) x‖) :
    (y, x) ∈ wolfeClopenKernelRelation ν d := by
  apply wolfeClopenKernelRelation_mem_of_atom N ν y x _ hatom
  rw [hone, RCLike.one_re]
  linarith

end Posets
