import Posets.WolfePreservationBlockJointPhaseDiscard

/-! The fixed phase supplies a continuous nearly-positive measure family,
and a compact domain of continuously varying normalized kernel rows. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

local instance wolfePhaseRowsDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance
local instance wolfePhaseRowsDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance

def wolfeJointPhaseMeasure (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZero 𝕜 (K × L)) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    WeakDual 𝕜 (JLMS.CZero 𝕜 K) :=
  weakStarAdjoint (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 K) (wolfeJointPhaseTotal S f)) μ

theorem wolfeJointPhaseMeasure_continuous
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L)) :
    Continuous (wolfeJointPhaseMeasure S f) := weakStarAdjoint_continuous _

theorem wolfeJointPhaseMeasure_coordinate (M : JLMS.AtomicDualModel 𝕜 K)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (y : K) :
    M.representation (WeakDual.toStrongDual (wolfeJointPhaseMeasure S f μ)) y =
      M.representation (WeakDual.toStrongDual μ) y * wolfeJointPhaseTotal S f y :=
  wolfeAtomicCoordinate_multiply M _ _ y

theorem wolfeJointPhaseMeasure_one
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    wolfeJointPhaseMeasure S f μ (wolfeSourceBlock univ isClopen_univ) = wolfeJointLift S μ f := by
  change μ (wolfeJointPhaseTotal S f * wolfeSourceBlock univ isClopen_univ) = _
  have he : wolfeJointPhaseTotal S f * wolfeSourceBlock univ isClopen_univ =
      wolfeJointPhaseTotal S f := by ext y; simp
  rw [he]
  rfl

theorem wolfeJointPhaseMeasure_norm_le_variation
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (hf : ‖f‖ ≤ 1) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    ‖WeakDual.toStrongDual (wolfeJointPhaseMeasure S f μ)‖ ≤ wolfeJointVariation S μ := by
  rw [← M.representation.norm_map, JLMS.ellOneOn_norm_eq_tsum,
    wolfeJointVariation_eq_atomic M N P S μ]
  apply (JLMS.ellOneOn_summable_norm _).tsum_le_tsum
  · intro y
    rw [wolfeJointPhaseMeasure_coordinate, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((wolfeJointPhaseTotal_apply_le_row N S f y).trans
        (wolfeJointPhaseKernel_row_norm_le N S f hf y)) (norm_nonneg _)
  · exact ((JLMS.ellOneOn_summable_norm _).mul_right ‖S‖).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun y => mul_le_mul_of_nonneg_left (wolfeAtomicCrossRow_norm_le N S y) (norm_nonneg _))

theorem wolfeJointPhaseMeasure_defect_le
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (hf : ‖f‖ ≤ 1) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    ‖WeakDual.toStrongDual (wolfeJointPhaseMeasure S f μ)‖ -
        RCLike.re (wolfeJointPhaseMeasure S f μ (wolfeSourceBlock univ isClopen_univ)) ≤
      wolfeJointVariation S μ - RCLike.re (wolfeJointLift S μ f) := by
  rw [wolfeJointPhaseMeasure_one]
  exact sub_le_sub_right (wolfeJointPhaseMeasure_norm_le_variation M N P S f hf μ) _

def wolfeJointPhaseGoodRows (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ κ : ℝ) : Set K :=
  {y | ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖ ≤
      (1 + τ) * ‖wolfeJointPhaseTotal S f y‖ ∧ κ ≤ ‖wolfeJointPhaseTotal S f y‖}

theorem wolfeJointPhaseGoodRows_isClosed (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L)) (τ κ : ℝ) :
    IsClosed (wolfeJointPhaseGoodRows N S f τ κ) := by
  have hr : LowerSemicontinuous
      (fun y => ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖) := by
    apply lowerSemicontinuous_iff_isClosed_preimage.mpr
    intro r
    have hc := (WeakDual.isClosed_closedBall
      (0 : StrongDual 𝕜 (JLMS.CZero 𝕜 L)) r).preimage
        ((weakStarAdjoint_continuous (wolfeJointPhaseKernel S f)).comp wolfeDirac_continuous)
    simpa only [Set.preimage, Metric.mem_closedBall, dist_zero_right,
      wolfeAtomicCrossRow, LinearIsometryEquiv.norm_map] using hc
  have ht : Continuous (fun y => -((1 + τ) * ‖wolfeJointPhaseTotal S f y‖)) :=
    (continuous_const.mul (wolfeJointPhaseTotal S f).continuous.norm).neg
  have hh := (hr.add ht.lowerSemicontinuous).isClosed_preimage (0 : ℝ)
  have he : wolfeJointPhaseGoodRows N S f τ κ =
      {y | ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖ +
        -((1 + τ) * ‖wolfeJointPhaseTotal S f y‖) ≤ 0} ∩
      {y | κ ≤ ‖wolfeJointPhaseTotal S f y‖} := by
    ext y
    simp only [wolfeJointPhaseGoodRows, mem_setOf_eq, mem_inter_iff]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he]
  exact hh.inter (isClosed_le continuous_const (wolfeJointPhaseTotal S f).continuous.norm)

def wolfeJointPhaseNormalizedRows (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L)) (τ κ : ℝ)
    (y : wolfeJointPhaseGoodRows N S f τ κ) : WeakDual 𝕜 (JLMS.CZero 𝕜 L) :=
  (wolfeJointPhaseTotal S f y.val)⁻¹ • weakStarAdjoint (wolfeJointPhaseKernel S f) (wolfeDirac y.val)

theorem wolfeJointPhaseNormalizedRows_continuous (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Continuous (wolfeJointPhaseNormalizedRows N S f τ κ) := by
  apply Continuous.smul
  · apply ((wolfeJointPhaseTotal S f).continuous.comp continuous_subtype_val).inv₀
    intro y
    exact norm_pos_iff.mp (hκ.trans_le y.property.2)
  · exact ((weakStarAdjoint_continuous (wolfeJointPhaseKernel S f)).comp
      wolfeDirac_continuous).comp continuous_subtype_val

theorem wolfeJointPhaseNormalizedRows_one (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ : ℝ) {κ : ℝ} (hκ : 0 < κ) (y : wolfeJointPhaseGoodRows N S f τ κ) :
    wolfeJointPhaseNormalizedRows N S f τ κ y (wolfeSourceBlock univ isClopen_univ) = 1 := by
  change (wolfeJointPhaseTotal S f y.val)⁻¹ *
    (wolfeJointPhaseKernel S f (wolfeSourceBlock univ isClopen_univ) y.val) = 1
  rw [← wolfeJointPhaseTotal_eq_kernel_one]
  exact inv_mul_cancel₀ (norm_pos_iff.mp (hκ.trans_le y.property.2))

theorem wolfeJointPhaseNormalizedRows_norm_le (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ : ℝ) {κ : ℝ} (hκ : 0 < κ) (y : wolfeJointPhaseGoodRows N S f τ κ) :
    ‖WeakDual.toStrongDual (wolfeJointPhaseNormalizedRows N S f τ κ y)‖ ≤ 1 + τ := by
  change ‖(wolfeJointPhaseTotal S f y.val)⁻¹ •
    ((JLMS.evaluation y.val).comp (wolfeJointPhaseKernel S f))‖ ≤ _
  rw [norm_smul, norm_inv, ← N.representation.norm_map]
  change (‖wolfeJointPhaseTotal S f y.val‖)⁻¹ *
    ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y.val‖ ≤ _
  have hy := y.property.1
  have hh := hκ.trans_le y.property.2
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ hh).mpr hy

end Posets
