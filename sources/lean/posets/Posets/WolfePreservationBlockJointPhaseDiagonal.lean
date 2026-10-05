import Posets.WolfePreservationBlockJointPhase

/-! A single phase test retains a uniformly large real diagonal fibre of
the joint measure. This is a diagonal lower bound, not an identity assertion
for the phase-modified marginal. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L X : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationJoint_diagonal_mass
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (x : L) :
    ‖c‖ ≤ wolfeJointMass P S (wolfeFactorizationLift T R c x) univ {x} := by
  let a := M.representation (WeakDual.toStrongDual (wolfeFactorizationLift T R c x))
  let b := wolfeAtomicCrossRow N S
  have hs : Summable (fun y => ‖a y * b y x‖) :=
    ((JLMS.ellOneOn_summable_norm a).mul_right ‖S‖).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun y => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (wolfeAtomicCrossRow_apply_le N S y x) (norm_nonneg _))
  have hn := (wolfeFactorizationLift_atomic_identity M N T R S hfactor c x).norm_le_of_bounded
    hs.hasSum (fun y => le_rfl)
  rw [wolfeJointMass_eq_atomic M N P S]
  simpa only [JLMS.restrictionL1_apply, JLMS.restrictL1_apply, mem_univ, if_true,
    wolfeMass_singleton, norm_mul, a, b, wolfeAtomicCrossRow] using hn

theorem wolfeFactorizationJoint_phase_diagonal_lower
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (x : L) (f : JLMS.CZero 𝕜 (K × L)) (hf : ‖f‖ ≤ 1) :
    ‖c‖ - (wolfeJointVariation S (wolfeFactorizationLift T R c x) -
      RCLike.re (wolfeJointLift S (wolfeFactorizationLift T R c x) f)) ≤
      RCLike.re (JLMS.atomicRestriction P (univ ×ˢ {x})
        (WeakDual.toStrongDual (wolfeJointLift S (wolfeFactorizationLift T R c x))) f) := by
  have hmass := wolfeFactorizationJoint_diagonal_mass M N P T R S hfactor c x
  have hphase := wolfePhaseRestriction_re_lower P
    (wolfeJointLift S (wolfeFactorizationLift T R c x)) f hf (univ ×ˢ {x})
  change wolfeJointMass P S (wolfeFactorizationLift T R c x) univ {x} -
    (wolfeJointVariation S (wolfeFactorizationLift T R c x) -
      RCLike.re (wolfeJointLift S (wolfeFactorizationLift T R c x) f)) ≤ _ at hphase
  linarith

end Posets
