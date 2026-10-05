import Posets.WolfePreservationBlockJointPhaseCoordinates

/-! The fixed global phase defect bounds the weighted failure of kernel
rows to have their variation equal the modulus of their total mass. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

def wolfeJointPhaseTotal (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) : JLMS.CZero 𝕜 K := wolfeJointCZeroOperator S f

theorem wolfeJointPhaseTotal_eq_kernel_one
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L)) :
    wolfeJointPhaseTotal S f =
      wolfeJointPhaseKernel S f (wolfeSourceBlock (univ : Set L) isClopen_univ) := by
  rw [wolfeJointPhaseKernel_apply]
  congr 1
  ext z
  rcases z with ⟨y, x⟩
  simp [ZeroAtInftyContinuousMap.mul_apply, wolfeJointSecondPullback_apply]

theorem wolfeJointPhaseTotal_apply_le_row
    (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L)) (y : K) :
    ‖wolfeJointPhaseTotal S f y‖ ≤ ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖ := by
  rw [wolfeJointPhaseTotal_eq_kernel_one]
  let φ := (JLMS.evaluation (𝕜 := 𝕜) y).comp (wolfeJointPhaseKernel S f)
  have h := φ.le_opNorm (wolfeSourceBlock (𝕜 := 𝕜) (univ : Set L) isClopen_univ)
  have hf := wolfeSourceBlock_norm_le (𝕜 := 𝕜) (univ : Set L) isClopen_univ
  have hn : ‖φ‖ = ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖ :=
    (N.representation.norm_map φ).symm
  have hb := mul_le_mul_of_nonneg_left hf (norm_nonneg φ)
  change ‖φ (wolfeSourceBlock univ isClopen_univ)‖ ≤ _
  rw [← hn]
  linarith

theorem wolfeJointPhaseKernel_row_norm_le
    (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) (hf : ‖f‖ ≤ 1) (y : K) :
    ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖ ≤ ‖wolfeAtomicCrossRow N S y‖ := by
  rw [JLMS.ellOneOn_norm_eq_tsum, JLMS.ellOneOn_norm_eq_tsum]
  apply (JLMS.ellOneOn_summable_norm _).tsum_le_tsum _ (JLMS.ellOneOn_summable_norm _)
  intro x
  rw [wolfeJointPhaseKernel_coordinate, norm_mul]
  have hp := (JLMS.norm_CZero_apply_le f (y, x)).trans hf
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg _)

theorem wolfeJointPhase_weighted_row_defect_le
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (f : JLMS.CZero 𝕜 (K × L)) (hf : ‖f‖ ≤ 1) :
    (∑' y, ‖M.representation (WeakDual.toStrongDual μ) y‖ *
      (‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖ - ‖wolfeJointPhaseTotal S f y‖)) ≤
      wolfeJointVariation S μ - RCLike.re (wolfeJointLift S μ f) := by
  let a := M.representation (WeakDual.toStrongDual μ)
  let b := wolfeAtomicCrossRow N S
  let b' := wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f)
  let h := wolfeJointPhaseTotal S f
  have hsum : Summable (fun y => ‖a y‖ * ‖b y‖) :=
    ((JLMS.ellOneOn_summable_norm a).mul_right ‖S‖).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun y => mul_le_mul_of_nonneg_left (wolfeAtomicCrossRow_norm_le N S y) (norm_nonneg _))
  have hpair := RCLike.reCLM.hasSum (JLMS.atomicDual_apply_hasSum M (WeakDual.toStrongDual μ) h)
  have hdiff := hsum.hasSum.sub hpair
  change HasSum (fun y => ‖a y‖ * ‖b y‖ - RCLike.re (a y * h y))
    ((∑' y, ‖a y‖ * ‖b y‖) - RCLike.re (μ h)) at hdiff
  have hnonneg (y : K) : 0 ≤ ‖a y‖ * (‖b' y‖ - ‖h y‖) :=
    mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (wolfeJointPhaseTotal_apply_le_row N S f y))
  have hbound (y : K) : ‖a y‖ * (‖b' y‖ - ‖h y‖) ≤
      ‖a y‖ * ‖b y‖ - RCLike.re (a y * h y) := by
    have hr := wolfeJointPhaseKernel_row_norm_le N S f hf y
    have hre := RCLike.re_le_norm (a y * h y)
    rw [norm_mul] at hre
    nlinarith [norm_nonneg (a y)]
  have hd : Summable (fun y => ‖a y‖ * (‖b' y‖ - ‖h y‖)) :=
    hdiff.summable.of_nonneg_of_le hnonneg hbound
  have hle := hd.tsum_le_tsum hbound hdiff.summable
  rw [hdiff.tsum_eq] at hle
  change (∑' y, ‖a y‖ * (‖b' y‖ - ‖h y‖)) ≤
    (∑' y, ‖M.representation (WeakDual.toStrongDual μ) y‖ *
      ‖wolfeAtomicCrossRow N S y‖) - RCLike.re (μ h) at hle
  rw [← wolfeJointVariation_eq_atomic M N P S μ] at hle
  exact hle

end Posets
