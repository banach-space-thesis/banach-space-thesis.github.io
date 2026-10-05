import Posets.WolfePreservationBlockJointPhaseDefect

/-! A uniform weighted bound for the rows discarded by near-positivity.
The error is charged to the single global phase defect. -/

noncomputable section
open Set Topology
namespace Posets

theorem wolfe_weighted_bad_rows_bound {I : Type*} (a b h : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 ≤ h i) (hhb : ∀ i, h i ≤ b i)
    (hs : Summable (fun i => a i * b i)) {τ : ℝ} (hτ : 0 < τ) :
    τ * (∑' i, if (1 + τ) * h i < b i then a i * b i else 0) ≤
      (1 + τ) * (∑' i, a i * (b i - h i)) := by
  classical
  have hn (i : I) : 0 ≤ a i * b i := mul_nonneg (ha i) ((hh i).trans (hhb i))
  have hd : Summable (fun i => a i * (b i - h i)) :=
    hs.of_nonneg_of_le (fun i => mul_nonneg (ha i) (sub_nonneg.mpr (hhb i)))
      (fun i => mul_le_mul_of_nonneg_left (sub_le_self _ (hh i)) (ha i))
  have hr : Summable (fun i => if (1 + τ) * h i < b i then a i * b i else 0) := by
    apply hs.of_nonneg_of_le
    · intro i; split_ifs
      · exact hn i
      · exact le_rfl
    · intro i; split_ifs <;> simp_all
  have hp (i : I) :
      τ * (if (1 + τ) * h i < b i then a i * b i else 0) ≤
        (1 + τ) * (a i * (b i - h i)) := by
    split_ifs with hi
    · have hm := mul_le_mul_of_nonneg_left hi.le (ha i)
      nlinarith
    · have hz := mul_nonneg (ha i) (sub_nonneg.mpr (hhb i))
      simpa only [mul_zero] using mul_nonneg (by linarith : 0 ≤ 1 + τ) hz
  have ht := (hr.mul_left τ).tsum_le_tsum hp (hd.mul_left (1 + τ))
  simpa only [tsum_mul_left] using ht

variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

theorem wolfeJointPhase_bad_rows_bound
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (f : JLMS.CZero 𝕜 (K × L)) (hf : ‖f‖ ≤ 1)
    {τ : ℝ} (hτ : 0 < τ) :
    τ * (∑' y, if (1 + τ) * ‖wolfeJointPhaseTotal S f y‖ <
        ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖ then
      ‖M.representation (WeakDual.toStrongDual μ) y‖ *
        ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖ else 0) ≤
      (1 + τ) * (wolfeJointVariation S μ - RCLike.re (wolfeJointLift S μ f)) := by
  have hs : Summable (fun y => ‖M.representation (WeakDual.toStrongDual μ) y‖ *
      ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y‖) :=
    ((JLMS.ellOneOn_summable_norm (M.representation (WeakDual.toStrongDual μ))).mul_right
      ‖wolfeJointPhaseKernel S f‖).of_nonneg_of_le
        (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun y => mul_le_mul_of_nonneg_left
          (wolfeAtomicCrossRow_norm_le N (wolfeJointPhaseKernel S f) y) (norm_nonneg _))
  exact (wolfe_weighted_bad_rows_bound _ _ _ (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) (wolfeJointPhaseTotal_apply_le_row N S f) hs hτ).trans
      (mul_le_mul_of_nonneg_left (wolfeJointPhase_weighted_row_defect_le M N P S μ f hf)
        (by positivity))

end Posets
