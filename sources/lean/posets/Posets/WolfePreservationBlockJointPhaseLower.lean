import Posets.WolfePreservationBlockJointPhaseSections

/-! Uniform positive section mass for factorization rows. All analytic
losses are explicit and may be fixed before choosing the ordinal-rank core. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L X : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationJoint_phase_section_lower
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hn : ‖c‖ * ‖R‖ ≤ 1)
    (f : JLMS.CZero 𝕜 (K × L)) (hf : ‖f‖ ≤ 1)
    {τ κ δ η : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (hηbudget : (1 + (1 + τ) / τ) * η ≤ ‖c‖ / 8)
    (hκbudget : (1 + τ) * κ * ‖T‖ ≤ ‖c‖ / 8)
    (hδbudget : δ * (‖T‖ * ‖S‖) ≤ ‖c‖ / 8)
    (x : L) (hdefect : wolfeJointVariation S (wolfeFactorizationLift T R c x) -
      RCLike.re (wolfeJointLift S (wolfeFactorizationLift T R c x) f) ≤ η)
    (Z : Set K)
    (hZ : ∀ y, y ∈ wolfeJointPhaseGoodRows N S f τ κ →
      δ * ‖wolfeJointPhaseTotal S f y‖ ≤ ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y x‖ →
        y ∈ Z) :
    ‖c‖ / 4 ≤ wolfeMass M (wolfeJointPhaseMeasure S f (wolfeFactorizationLift T R c x)) Z := by
  let μ := wolfeFactorizationLift T R c x
  let D := wolfeJointVariation S μ - RCLike.re (wolfeJointLift S μ f)
  let m := wolfeMass M (wolfeJointPhaseMeasure S f μ) Z
  have hb := wolfeJointPhase_section_budget M N P S μ f hf hτ hκ hδ x Z hZ
  have hd := wolfeJointPhaseKernel_factorization_diagonal_lower M N P T R S hfactor c x f hf
  have hμ := wolfeFactorizationLift_norm_le T R c hn x
  have hσ := (wolfeJointPhaseMeasure_norm_le_variation M N P S f hf μ).trans
    (wolfeFactorizationJoint_norm_le T R S c hn x)
  have hsmall := (mul_le_mul_of_nonneg_left hμ
    (mul_nonneg (by linarith : 0 ≤ 1 + τ) hκ)).trans hκbudget
  have hatom := (mul_le_mul_of_nonneg_left hσ hδ).trans hδbudget
  have hD := (mul_le_mul_of_nonneg_left hdefect
    (by positivity : 0 ≤ 1 + (1 + τ) / τ)).trans hηbudget
  have hm0 : 0 ≤ m := wolfeMass_nonneg M _ Z
  have hm : (1 + τ) * m ≤ 2 * m := mul_le_mul_of_nonneg_right (by linarith) hm0
  change ‖c‖ - D ≤ _ at hd
  change _ ≤ (1 + τ) * m + ((1 + τ) / τ) * D +
    (1 + τ) * κ * ‖WeakDual.toStrongDual μ‖ +
      δ * ‖WeakDual.toStrongDual (wolfeJointPhaseMeasure S f μ)‖ at hb
  change (1 + (1 + τ) / τ) * D ≤ _ at hD
  change ‖c‖ / 4 ≤ m
  nlinarith

end Posets
