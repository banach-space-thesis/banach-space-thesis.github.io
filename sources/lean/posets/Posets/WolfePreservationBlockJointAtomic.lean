import Posets.WolfePreservationBlockJointVariation

/-! The joint functional has the genuine atomic coefficients
μ(y) (S*δ_y)(x). Consequently its norm is the weighted total variation
used in the finite-loss localization argument. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜]

theorem wolfeJointCoefficients_summable (a : JLMS.ellOneOn 𝕜 K)
    (b : K → JLMS.ellOneOn 𝕜 L) {B : ℝ} (hb : ∀ y, ‖b y‖ ≤ B) :
    Summable (fun z : K × L => ‖a z.1 * b z.1 z.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro y
    simpa only [norm_mul] using (JLMS.ellOneOn_summable_norm (b y)).mul_left ‖a y‖
  · have he (y : K) : (∑' x, ‖a y * b y x‖) = ‖a y‖ * ‖b y‖ := by
      simp only [norm_mul, tsum_mul_left, ← JLMS.ellOneOn_norm_eq_tsum]
    simp_rw [he]
    exact ((JLMS.ellOneOn_summable_norm a).mul_right B).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun y => mul_le_mul_of_nonneg_left (hb y) (norm_nonneg _))

def wolfeJointCoefficients (a : JLMS.ellOneOn 𝕜 K)
    (b : K → JLMS.ellOneOn 𝕜 L) {B : ℝ} (hb : ∀ y, ‖b y‖ ≤ B) : JLMS.ellOneOn 𝕜 (K × L) :=
  ⟨fun z => a z.1 * b z.1 z.2, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one] using wolfeJointCoefficients_summable a b hb⟩

@[simp] theorem wolfeJointCoefficients_apply (a : JLMS.ellOneOn 𝕜 K)
    (b : K → JLMS.ellOneOn 𝕜 L) {B : ℝ} (hb : ∀ y, ‖b y‖ ≤ B) (y : K) (x : L) :
    wolfeJointCoefficients a b hb (y, x) = a y * b y x := rfl

theorem wolfeJointCoefficients_norm (a : JLMS.ellOneOn 𝕜 K)
    (b : K → JLMS.ellOneOn 𝕜 L) {B : ℝ} (hb : ∀ y, ‖b y‖ ≤ B) :
    ‖wolfeJointCoefficients a b hb‖ = ∑' y, ‖a y‖ * ‖b y‖ := by
  rw [JLMS.ellOneOn_norm_eq_tsum]
  rw [(JLMS.ellOneOn_summable_norm (wolfeJointCoefficients a b hb)).tsum_prod]
  simp only [wolfeJointCoefficients_apply, norm_mul, tsum_mul_left, ← JLMS.ellOneOn_norm_eq_tsum]

variable [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

theorem wolfeJointLift_atomicFunctional
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    WeakDual.toStrongDual (wolfeJointLift S μ) = JLMS.atomicFunctional
      (wolfeJointCoefficients (M.representation (WeakDual.toStrongDual μ))
        (wolfeAtomicCrossRow N S) (wolfeAtomicCrossRow_norm_le N S)) := by
  apply ContinuousLinearMap.ext
  intro f
  let a := M.representation (WeakDual.toStrongDual μ)
  let b := wolfeAtomicCrossRow N S
  change μ (wolfeJointCZeroOperator S f) =
    ∑' z : K × L, wolfeJointCoefficients a b (wolfeAtomicCrossRow_norm_le N S) z * f z
  rw [(JLMS.summable_atomic_values
    (wolfeJointCoefficients a b (wolfeAtomicCrossRow_norm_le N S)) f).tsum_prod]
  have he (y : K) : (∑' x, wolfeJointCoefficients a b (wolfeAtomicCrossRow_norm_le N S)
      (y, x) * f (y, x)) = a y * wolfeJointCZeroOperator S f y := by
    simp only [wolfeJointCoefficients_apply, mul_assoc, tsum_mul_left]
    rw [wolfeJointCZeroOperator_apply]
    congr 1
    exact (JLMS.atomicDual_apply_hasSum N ((JLMS.evaluation y).comp S)
      ((JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L))
        (((JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K × L)).symm f).curry y))).tsum_eq
  simp_rw [he]
  exact (JLMS.atomicDual_apply_hasSum M (WeakDual.toStrongDual μ) _).tsum_eq.symm

theorem wolfe_atomicFunctional_eq_representation_symm {Y : Type*} [TopologicalSpace Y]
    (P : JLMS.AtomicDualModel 𝕜 Y) (a : JLMS.ellOneOn 𝕜 Y) :
    JLMS.atomicFunctional a = P.representation.symm a := by
  apply ContinuousLinearMap.ext
  intro f
  have h := (JLMS.atomicDual_apply_hasSum P (P.representation.symm a) f).tsum_eq
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

theorem wolfeJointVariation_eq_atomic
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    wolfeJointVariation S μ = ∑' y,
      ‖M.representation (WeakDual.toStrongDual μ) y‖ * ‖wolfeAtomicCrossRow N S y‖ := by
  unfold wolfeJointVariation
  rw [wolfeJointLift_atomicFunctional M N S μ, wolfe_atomicFunctional_eq_representation_symm P,
    P.representation.symm.norm_map, wolfeJointCoefficients_norm]

end Posets
