import SurveyStatements.P5OperatorReductionPairing
import SurveyStatements.P5OperatorReductionFiniteDisjointification
import SurveyStatements.P5OperatorReductionSignedLpGrowthScaling

/-! Uniform small restrictions of actual packet-averaged shadows of an
arbitrary mixed operator. The inputs may vary with the index and need only
the genuine uniform pointwise bound of raw signed Haar packets. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
open SurveyStatements.P5Support.Grothendieck
variable {𝕜 ι : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def packetShadow (k : ι → ℕ)
    (f : ∀ i, (Fin (k i) → Bool) → Lp 𝕜 p unitIntervalMeasure)
    (η : ∀ i, (Fin (k i) → Bool) → ℝ → 𝕜)
    (hη : ∀ i θ, StronglyMeasurable (η i θ))
    (hb : ∀ i θ x, ‖η i θ x‖ ≤ 1)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (g : Lp 𝕜 1 unitIntervalMeasure) (i : ι) : Lp 𝕜 1 unitIntervalMeasure :=
  vectorMean (𝕜 := 𝕜) (fun θ => weightedOuterReader (η i θ) (hη i θ) (hb i θ)
    (T (tensorWith g (f i θ))))

theorem uniformSmallRestrictions_packetShadow (hp : p ≠ ∞) (k : ι → ℕ)
    (f : ∀ i, (Fin (k i) → Bool) → Lp 𝕜 p unitIntervalMeasure)
    (hf : ∀ i θ, ∀ᵐ x ∂unitIntervalMeasure, ‖f i θ x‖ ≤ 1)
    (η : ∀ i, (Fin (k i) → Bool) → ℝ → 𝕜)
    (hη : ∀ i θ, StronglyMeasurable (η i θ))
    (hb : ∀ i θ x, ‖η i θ x‖ ≤ 1)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (g : Lp 𝕜 1 unitIntervalMeasure) :
    UniformSmallRestrictions (packetShadow k f η hη hb T g) := by
  by_contra hfail
  obtain ⟨ε, hε, hdisjoint⟩ := finite_disjointification_of_not_uniformSmallRestrictions
    (packetShadow k f η hη hb T g) hfail
  let C : ℝ := ‖T‖ * ‖g‖
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨N, hN, hsmall⟩ := uniform_signedLp_unit_mean_ratio_small
    (𝕜 := 𝕜) (μ := unitIntervalMeasure) hp (ε / (C + 1)) (div_pos hε hC1)
  obtain ⟨v, s, hs, hd, hmass⟩ := hdisjoint N
  obtain ⟨π, hnorm, hπ⟩ := exists_disjoint_norming_readers Finset.univ s hs
    (fun i _ j _ hij => hd i j hij) (fun i => packetShadow k f η hη hb T g (v i))
  have hmean (i : Fin N) :
      RCLike.re (π i (packetShadow k f η hη hb T g (v i))) =
        mean (fun θ : Fin (k (v i)) → Bool => RCLike.re (π i
          (weightedOuterReader (η (v i) θ) (hη (v i) θ) (hb (v i) θ)
            (T (tensorWith g (f (v i) θ)))))) :=
    real_pairing_vectorMean (π i) _
  choose σ hσ using (fun i : Fin N => exists_mean_le
    (fun θ : Fin (k (v i)) → Bool => RCLike.re (π i
      (weightedOuterReader (η (v i) θ) (hη (v i) θ) (hb (v i) θ)
        (T (tensorWith g (f (v i) θ)))))))
  have hlarge (i : Fin N) : ε < RCLike.re (π i
      (weightedOuterReader (η (v i) (σ i)) (hη (v i) (σ i)) (hb (v i) (σ i))
        (T (tensorWith g (f (v i) (σ i)))))) := by
    have h := hmass i (hs i)
    rw [norm_l1_restriction] at h
    have heq := congrArg RCLike.re (hnorm i)
    simp only [RCLike.ofReal_re] at heq
    rw [← heq] at h
    exact h.trans_le ((hmean i).trans_le (hσ i))
  have hNu : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hsum : (N : ℝ) * ε < ∑ i, RCLike.re (π i
      (weightedOuterReader (η (v i) (σ i)) (hη (v i) (σ i)) (hb (v i) (σ i))
        (T (tensorWith g (f (v i) (σ i)))))) := by
    simpa using Finset.sum_lt_sum_of_nonempty hNu (fun i _ => hlarge i)
  have hreal : (∑ i, RCLike.re (π i
      (weightedOuterReader (η (v i) (σ i)) (hη (v i) (σ i)) (hb (v i) (σ i))
        (T (tensorWith g (f (v i) (σ i))))))) ≤
      ‖∑ i, π i
        (weightedOuterReader (η (v i) (σ i)) (hη (v i) (σ i)) (hb (v i) (σ i))
          (T (tensorWith g (f (v i) (σ i)))))‖ := by
    rw [← map_sum]
    exact RCLike.re_le_norm _
  have hpair := norm_mixed_diagonal_pairing_le T g π (by simpa using hπ)
    (fun i => η (v i) (σ i)) (fun i => hη (v i) (σ i))
    (fun i => hb (v i) (σ i)) (fun i => f (v i) (σ i))
  have hgrowth := hsmall N le_rfl (fun i => f (v i) (σ i)) (fun i => hf (v i) (σ i))
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hgrowth' := (div_lt_iff₀ hNR).mp hgrowth
  have hfrac : C * (ε / (C + 1)) < ε := by
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ hC1).mpr (by nlinarith)
  have hbound : C * mean
      (fun θ : Fin N → Bool => ‖∑ i, signedValue (θ i) (f (v i) (σ i))‖) <
        (N : ℝ) * ε := by
    calc
      _ ≤ C * (ε / (C + 1) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hgrowth'.le hC
      _ = (C * (ε / (C + 1))) * (N : ℝ) := by ring
      _ < ε * (N : ℝ) := mul_lt_mul_of_pos_right hfrac hNR
      _ = _ := mul_comm _ _
  exact (lt_irrefl ((N : ℝ) * ε)
    ((hsum.trans_le (hreal.trans hpair)).trans hbound)).elim

end SurveyStatements.P5OperatorReduction
