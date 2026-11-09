import SurveyStatements.P4BaireOneAdjoint
import SurveyStatements.P4TailConvexRCLike
import SurveyStatements.P4BaireFiniteRank
import SurveyStatements.P4BidualApproximation
import SurveyStatements.P4ConvexTails

/-! Common convex tails give actual two-sided finite-rank approximations. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 1024

open Set Filter Topology TopologicalSpace
open scoped BigOperators

namespace SurveyStatements.P4

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def weakStarDualUnitBall (𝕜 Y : Type*) [RCLike 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] : Set (WeakDual 𝕜 Y) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1

instance weakStarDualUnitBall_compactSpace : CompactSpace (weakStarDualUnitBall 𝕜 Y) :=
  isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 Y) 1)

lemma weakStarDualUnitBall_norm_le (φ : weakStarDualUnitBall 𝕜 Y) :
    ‖WeakDual.toStrongDual φ.val‖ ≤ 1 := by
  simpa only [weakStarDualUnitBall, Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right] using φ.property

theorem exists_twoSided_finiteRank_approximants [SeparableSpace Y]
    (hBAP : HasBoundedApproximationProperty 𝕜 Y)
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ → X →L[𝕜] Y,
      (∀ n, HasFiniteRank 𝕜 (A n)) ∧ (∀ n, ‖A n‖ ≤ C) ∧
      (∀ x : X, Tendsto (fun n => A n x) atTop (𝓝 (T x))) ∧
      (∀ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
        Tendsto (fun n => bidualMap (A n) ξ) atTop (𝓝 (bidualMap T ξ))) ∧
      ∀ φ : StrongDual 𝕜 Y,
        Tendsto (fun n => banachAdjoint (A n) φ) atTop (𝓝 (banachAdjoint T φ)) := by
  classical
  obtain ⟨C, hC, P, hfinite, hnorm, hstrong⟩ := hBAP.sequential
  let K := weakStarDualUnitBall 𝕜 Y
  let fseq : ℕ → C(K, StrongDual 𝕜 X) := fun n =>
    ⟨fun φ => banachAdjoint ((P n).comp T) (WeakDual.toStrongDual φ.val),
      (finiteRank_adjoint_weakStar_norm_continuous ((P n).comp T)
        ((hfinite n).comp_right T)).comp continuous_subtype_val⟩
  let f : K → StrongDual 𝕜 X := fun φ => banachAdjoint T (WeakDual.toStrongDual φ.val)
  have hfbound : ∀ n, ‖fseq n‖ ≤ C * ‖T‖ := by
    intro n
    apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).mpr
    intro φ
    change ‖(WeakDual.toStrongDual φ.val).comp ((P n).comp T)‖ ≤ C * ‖T‖
    calc
      _ ≤ ‖WeakDual.toStrongDual φ.val‖ * ‖(P n).comp T‖ :=
        (WeakDual.toStrongDual φ.val).opNorm_comp_le _
      _ ≤ 1 * ‖(P n).comp T‖ := mul_le_mul_of_nonneg_right
        (weakStarDualUnitBall_norm_le φ) (norm_nonneg _)
      _ ≤ C * ‖T‖ := by
        simpa only [one_mul] using ((P n).opNorm_comp_le T).trans
          (mul_le_mul_of_nonneg_right (hnorm n) (norm_nonneg _))
  have hfweak : ∀ φ (ξ : StrongDual 𝕜 (StrongDual 𝕜 X)),
      Tendsto (fun n => ξ (fseq n φ)) atTop (𝓝 (ξ (f φ))) := by
    intro φ ξ
    exact ((ContinuousLinearMap.apply 𝕜 𝕜 (WeakDual.toStrongDual φ.val)).continuous.tendsto
      (bidualMap T ξ)).comp (bidual_approximants_tendsto P hstrong T hT ξ)
  obtain ⟨F, a, ha, hsum, htail, hadjoint⟩ := parameter_tail_convexification_rclike
    (𝕜 := 𝕜) fseq (C * ‖T‖) hfbound f hfweak
    (weaklyCompact_adjoint_isNormBaireOne_on T hT K)
  let S : ℕ → Y →L[𝕜] Y := fun k => finiteConvexCombination P (F k) (a k)
  have hSstrong : ∀ y, Tendsto (fun k => S k y) atTop (𝓝 y) :=
    finiteConvexCombination_tails_tendsto P hstrong F a (fun k n hn => ha k n) hsum htail
  have hconv (k : ℕ) (φ : StrongDual 𝕜 Y) :
      banachAdjoint ((S k).comp T) φ =
        ∑ n ∈ F k, a k n • banachAdjoint ((P n).comp T) φ := by
    ext x
    simp only [banachAdjoint_apply, S, finiteConvexCombination,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, map_sum, map_smul,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  have hunit : ∀ φ : K,
      Tendsto (fun k => banachAdjoint ((S k).comp T) (WeakDual.toStrongDual φ.val))
        atTop (𝓝 (banachAdjoint T (WeakDual.toStrongDual φ.val))) := by
    intro φ
    simpa only [hconv, fseq, f, ContinuousMap.coe_mk] using hadjoint φ
  refine ⟨C * ‖T‖, mul_nonneg hC (norm_nonneg _), fun k => (S k).comp T,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (finiteRank_finiteConvexCombination P hfinite (F k) (a k)).comp_right T
  · intro k
    exact ((S k).opNorm_comp_le T).trans (mul_le_mul_of_nonneg_right
      (norm_finiteConvexCombination_le P C hnorm (F k) (a k)
        (fun n hn => ha k n) (hsum k)) (norm_nonneg _))
  · intro x
    exact hSstrong (T x)
  · exact bidual_approximants_tendsto S hSstrong T hT
  · intro φ
    by_cases hφ : φ = 0
    · simp only [hφ, map_zero]
      exact tendsto_const_nhds
    have hr : 0 < ‖φ‖ := norm_pos_iff.mpr hφ
    let ψ : StrongDual 𝕜 Y := ((‖φ‖⁻¹ : ℝ) : 𝕜) • φ
    have hψ : ‖ψ‖ ≤ 1 := by
      dsimp only [ψ]
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hr),
        inv_mul_cancel₀ (ne_of_gt hr)]
    let θ : K := ⟨StrongDual.toWeakDual ψ,
      by change dist ψ 0 ≤ 1; simpa only [dist_zero_right] using hψ⟩
    have hscale : (‖φ‖ : 𝕜) • ψ = φ := by
      dsimp only [ψ]
      rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hr),
        RCLike.ofReal_one, one_smul]
    have h := (hunit θ).const_smul (‖φ‖ : 𝕜)
    change Tendsto (fun k => (‖φ‖ : 𝕜) • banachAdjoint ((S k).comp T) ψ)
      atTop (𝓝 ((‖φ‖ : 𝕜) • banachAdjoint T ψ)) at h
    simpa only [← map_smul, hscale] using h

end SurveyStatements.P4
