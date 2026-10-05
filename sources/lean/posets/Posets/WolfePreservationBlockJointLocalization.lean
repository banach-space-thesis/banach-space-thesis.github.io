import Posets.WolfePreservationBlockJointAtomic
import Posets.WolfePreservationNecessaryKernel

/-! Rectangular variation of the joint kernel. The source region and target
region remain explicit, so localization can retain all descendant source
regions at once. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

def wolfeJointMass (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (H : Set K) (V : Set L) : ℝ :=
  wolfeMass P (wolfeJointLift S μ) (H ×ˢ V)

theorem wolfeJointLift_coordinates
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    P.representation (WeakDual.toStrongDual (wolfeJointLift S μ)) =
      wolfeJointCoefficients (M.representation (WeakDual.toStrongDual μ))
        (wolfeAtomicCrossRow N S) (wolfeAtomicCrossRow_norm_le N S) := by
  rw [wolfeJointLift_atomicFunctional M N S μ,
    wolfe_atomicFunctional_eq_representation_symm P, P.representation.apply_symm_apply]

theorem wolfeJointMass_eq_atomic
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (H : Set K) (V : Set L) :
    wolfeJointMass P S μ H V = ∑' y,
      ‖JLMS.restrictionL1 H (M.representation (WeakDual.toStrongDual μ)) y‖ *
        wolfeMass N (weakStarAdjoint S (wolfeDirac y)) V := by
  unfold wolfeJointMass wolfeMass
  rw [JLMS.atomicRestriction_norm, wolfeJointLift_coordinates M N P S μ]
  let a := M.representation (WeakDual.toStrongDual μ)
  let b := wolfeAtomicCrossRow N S
  have hb (y : K) : ‖JLMS.restrictionL1 V (b y)‖ ≤ ‖S‖ :=
    (JLMS.restrictL1_norm_le V (b y)).trans (wolfeAtomicCrossRow_norm_le N S y)
  have he : JLMS.restrictionL1 (H ×ˢ V)
      (wolfeJointCoefficients a b (wolfeAtomicCrossRow_norm_le N S)) =
      wolfeJointCoefficients (JLMS.restrictionL1 H a)
        (fun y => JLMS.restrictionL1 V (b y)) hb := by
    ext z
    rcases z with ⟨y, x⟩
    by_cases hy : y ∈ H <;> by_cases hx : x ∈ V <;>
      simp [JLMS.restrictionL1_apply, JLMS.restrictL1_apply, wolfeJointCoefficients_apply,
        hy, hx]
  change ‖JLMS.restrictionL1 (H ×ˢ V)
    (wolfeJointCoefficients a b (wolfeAtomicCrossRow_norm_le N S))‖ = _
  rw [he, wolfeJointCoefficients_norm]
  apply tsum_congr
  intro y
  rw [JLMS.atomicRestriction_norm]
  rfl

theorem wolfeJointMass_target_compl (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (H : Set K) (V : Set L) :
    wolfeJointMass P S μ univ V =
      wolfeJointMass P S μ H V + wolfeJointMass P S μ Hᶜ V := by
  have he : (univ : Set K) ×ˢ V = (H ×ˢ V) ∪ (Hᶜ ×ˢ V) := by ext z; simp; tauto
  have hd : Disjoint (H ×ˢ V) (Hᶜ ×ˢ V) := by
    rw [Set.disjoint_left]
    exact fun _ h1 h2 => h2.1 h1.1
  unfold wolfeJointMass wolfeMass
  rw [he, JLMS.atomicRestriction_norm_union P _ _ hd]

theorem wolfeJointMass_source_compl (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (H : Set K) (V : Set L) :
    wolfeJointMass P S μ H univ =
      wolfeJointMass P S μ H V + wolfeJointMass P S μ H Vᶜ := by
  have he : H ×ˢ (univ : Set L) = (H ×ˢ V) ∪ (H ×ˢ Vᶜ) := by ext z; simp; tauto
  have hd : Disjoint (H ×ˢ V) (H ×ˢ Vᶜ) := by
    rw [Set.disjoint_left]
    exact fun _ h1 h2 => h2.2 h1.2
  unfold wolfeJointMass wolfeMass
  rw [he, JLMS.atomicRestriction_norm_union P _ _ hd]

theorem wolfeJointMass_outside_kernel_le
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (V : Set L) {δ : ℝ} (hδ : 0 ≤ δ) :
    wolfeJointMass P S μ (wolfeKernelRegion N S V δ)ᶜ V ≤
      δ * ‖WeakDual.toStrongDual μ‖ := by
  rw [wolfeJointMass_eq_atomic M N P S μ]
  let a := M.representation (WeakDual.toStrongDual μ)
  let H := (wolfeKernelRegion N S V δ)ᶜ
  have ht : Summable (fun y => δ * ‖a y‖) := (JLMS.ellOneOn_summable_norm a).mul_left δ
  have hle (y : K) : ‖JLMS.restrictionL1 H a y‖ *
      wolfeMass N (weakStarAdjoint S (wolfeDirac y)) V ≤ δ * ‖a y‖ := by
    by_cases hy : y ∈ H
    · have hv : wolfeMass N (weakStarAdjoint S (wolfeDirac y)) V ≤ δ := le_of_not_gt hy
      simp only [JLMS.restrictionL1_apply, JLMS.restrictL1_apply, hy, if_true]
      nlinarith [norm_nonneg (a y)]
    · simp only [JLMS.restrictionL1_apply, JLMS.restrictL1_apply, hy, if_false, norm_zero,
        zero_mul]
      exact mul_nonneg hδ (norm_nonneg _)
  have hs : Summable (fun y => ‖JLMS.restrictionL1 H a y‖ *
      wolfeMass N (weakStarAdjoint S (wolfeDirac y)) V) :=
    ht.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (by unfold wolfeMass; positivity)) hle
  have h := hs.tsum_le_tsum hle ht
  simpa only [tsum_mul_left, ← JLMS.ellOneOn_norm_eq_tsum, a,
    M.representation.norm_map] using h

end Posets
