import Posets.WolfePreservationBlockJointPhaseBudget

/-! Lower bounds for the mass of any section containing the good, large
normalized diagonal atoms. The section may be a union of quantile graphs. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

theorem wolfeJointPhase_section_budget
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (f : JLMS.CZero 𝕜 (K × L)) (hf : ‖f‖ ≤ 1)
    {τ κ δ : ℝ} (hτ : 0 < τ) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (x : L) (Z : Set K)
    (hZ : ∀ y, y ∈ wolfeJointPhaseGoodRows N S f τ κ →
      δ * ‖wolfeJointPhaseTotal S f y‖ ≤ ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y x‖ →
        y ∈ Z) :
    RCLike.re (N.representation ((WeakDual.toStrongDual μ).comp (wolfeJointPhaseKernel S f)) x) ≤
      (1 + τ) * wolfeMass M (wolfeJointPhaseMeasure S f μ) Z +
      ((1 + τ) / τ) * (wolfeJointVariation S μ - RCLike.re (wolfeJointLift S μ f)) +
      (1 + τ) * κ * ‖WeakDual.toStrongDual μ‖ +
      δ * ‖WeakDual.toStrongDual (wolfeJointPhaseMeasure S f μ)‖ := by
  classical
  let a := M.representation (WeakDual.toStrongDual μ)
  let b := wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f)
  let h := wolfeJointPhaseTotal S f
  have has : Summable (fun y => ‖a y‖) := JLMS.ellOneOn_summable_norm a
  have hab : Summable (fun y => ‖a y‖ * ‖b y‖) :=
    (has.mul_right ‖wolfeJointPhaseKernel S f‖).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun y => mul_le_mul_of_nonneg_left
        (wolfeAtomicCrossRow_norm_le N (wolfeJointPhaseKernel S f) y) (norm_nonneg _))
  have hlb (y : K) : ‖b y x‖ ≤ ‖b y‖ :=
    lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) _ x
  have hsum := wolfe_weighted_section_budget (fun y => ‖a y‖) (fun y => ‖b y‖)
    (fun y => ‖h y‖) (fun y => ‖b y x‖) Z (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (wolfeJointPhaseTotal_apply_le_row N S f) hlb has hab
      (by linarith : 0 ≤ 1 + τ) hκ hδ
      (fun y hb hk hl => hZ y ⟨hb, hk⟩ hl)
  have hnorm : (∑' y, ‖a y‖) = ‖WeakDual.toStrongDual μ‖ := by
    rw [← JLMS.ellOneOn_norm_eq_tsum, M.representation.norm_map]
  have hsig : (∑' y, ‖a y‖ * ‖h y‖) =
      ‖WeakDual.toStrongDual (wolfeJointPhaseMeasure S f μ)‖ := by
    rw [← M.representation.norm_map, JLMS.ellOneOn_norm_eq_tsum]
    apply tsum_congr
    intro y
    rw [wolfeJointPhaseMeasure_coordinate, norm_mul]
  have hmass : (∑' y, if y ∈ Z then ‖a y‖ * ‖h y‖ else 0) =
      wolfeMass M (wolfeJointPhaseMeasure S f μ) Z := by
    rw [wolfeMass_eq_tsum]
    apply tsum_congr
    intro y
    simp only [Set.indicator_apply, wolfeJointPhaseMeasure_coordinate, norm_mul]
    rfl
  rw [hnorm, hsig, hmass] at hsum
  have hbad := wolfeJointPhase_bad_rows_bound M N P S μ f hf hτ
  have hbad' : (∑' y, if (1 + τ) * ‖h y‖ < ‖b y‖ then ‖a y‖ * ‖b y‖ else 0) ≤
      ((1 + τ) / τ) * (wolfeJointVariation S μ - RCLike.re (wolfeJointLift S μ f)) := by
    have hbnd : (∑' y, if (1 + τ) * ‖h y‖ < ‖b y‖ then ‖a y‖ * ‖b y‖ else 0) ≤
        (1 + τ) * (wolfeJointVariation S μ - RCLike.re (wolfeJointLift S μ f)) / τ := by
      apply (le_div_iff₀ hτ).mpr
      simpa only [mul_comm] using hbad
    convert hbnd using 1 <;> ring
  have hpair := wolfeAtomicCrossRow_pairing M N (wolfeJointPhaseKernel S f)
    (WeakDual.toStrongDual μ) x
  have hlSum : Summable (fun y => ‖a y‖ * ‖b y x‖) := hab.of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun y => mul_le_mul_of_nonneg_left (hlb y) (norm_nonneg _))
  have hdiag : RCLike.re (N.representation
      ((WeakDual.toStrongDual μ).comp (wolfeJointPhaseKernel S f)) x) ≤
      ∑' y, ‖a y‖ * ‖b y x‖ := by
    have hr := RCLike.reCLM.hasSum hpair
    change HasSum (fun y => RCLike.re (a y * b y x))
      (RCLike.re (N.representation ((WeakDual.toStrongDual μ).comp (wolfeJointPhaseKernel S f)) x)) at hr
    rw [← hr.tsum_eq]
    apply hr.summable.tsum_le_tsum _ hlSum
    intro y
    simpa only [norm_mul] using RCLike.re_le_norm (a y * b y x)
  linarith

end Posets
