import SurveyStatements.P5OperatorReductionPacketShadows
import SurveyStatements.P5OperatorReductionInnerSlices

/-! Uniform norm bounds and full probability-theoretic uniform integrability
of the actual packet shadow family. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
open SurveyStatements.P5Support.Grothendieck
variable {𝕜 ι : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_vectorMean_le {Ω E : Type*} [Fintype Ω] [Nonempty Ω]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (v : Ω → E) :
    ‖vectorMean (𝕜 := 𝕜) v‖ ≤ mean (fun ω => ‖v ω‖) := by
  rw [vectorMean, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity), mean]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem norm_scalarLp_le_one_of_ae (f : Lp 𝕜 p unitIntervalMeasure)
    (hf : ∀ᵐ x ∂unitIntervalMeasure, ‖f x‖ ≤ 1) : ‖f‖ ≤ 1 := by
  have hconst : ‖Lp.const p unitIntervalMeasure (1 : 𝕜)‖ ≤ 1 := by
    simpa using Lp.norm_const_le (c := (1 : 𝕜)) (p := p) (μ := unitIntervalMeasure)
  apply (Lp.norm_le_norm_of_ae_le ?_).trans hconst
  filter_upwards [hf, Lp.coeFn_const p unitIntervalMeasure (1 : 𝕜)] with x hfx hx
  simpa only [hx, Function.const_apply, norm_one] using hfx

theorem norm_packetShadow_le (k : ι → ℕ)
    (f : ∀ i, (Fin (k i) → Bool) → Lp 𝕜 p unitIntervalMeasure)
    (hf : ∀ i θ, ∀ᵐ x ∂unitIntervalMeasure, ‖f i θ x‖ ≤ 1)
    (η : ∀ i, (Fin (k i) → Bool) → ℝ → 𝕜)
    (hη : ∀ i θ, StronglyMeasurable (η i θ))
    (hb : ∀ i θ x, ‖η i θ x‖ ≤ 1)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (g : Lp 𝕜 1 unitIntervalMeasure) (i : ι) :
    ‖packetShadow k f η hη hb T g i‖ ≤ ‖T‖ * ‖g‖ := by
  apply (norm_vectorMean_le _).trans
  apply (mean_mono (fun θ => ?_)).trans_eq (mean_const _)
  calc
    _ ≤ ‖T (tensorWith g (f i θ))‖ := by
      exact contraction_apply_bound (𝕜 := 𝕜) (X := MixedNorm 𝕜 p)
        (Y := Lp 𝕜 1 unitIntervalMeasure)
        (weightedOuterReader (𝕜 := 𝕜) (p := p) (E := Lp 𝕜 1 unitIntervalMeasure)
          (η i θ) (hη i θ) (hb i θ))
        (norm_weightedOuterReader_le (𝕜 := 𝕜) (p := p) (E := Lp 𝕜 1 unitIntervalMeasure)
          (η i θ) (hη i θ) (hb i θ)) (T (tensorWith g (f i θ)))
    _ ≤ ‖T‖ * ‖tensorWith g (f i θ)‖ := T.le_opNorm _
    _ = ‖T‖ * (‖g‖ * ‖f i θ‖) := by rw [norm_tensorWith 𝕜 p]
    _ ≤ _ := by
      simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_scalarLp_le_one_of_ae (f i θ) (hf i θ))
        (mul_nonneg (norm_nonneg T) (norm_nonneg g))

theorem uniformIntegrable_packetShadow (hp : p ≠ ∞) (k : ι → ℕ)
    (f : ∀ i, (Fin (k i) → Bool) → Lp 𝕜 p unitIntervalMeasure)
    (hf : ∀ i θ, ∀ᵐ x ∂unitIntervalMeasure, ‖f i θ x‖ ≤ 1)
    (η : ∀ i, (Fin (k i) → Bool) → ℝ → 𝕜)
    (hη : ∀ i θ, StronglyMeasurable (η i θ))
    (hb : ∀ i θ x, ‖η i θ x‖ ≤ 1)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (g : Lp 𝕜 1 unitIntervalMeasure) :
    UniformIntegrable (fun i x => packetShadow k f η hη hb T g i x) 1
      unitIntervalMeasure := by
  refine ⟨fun i => Lp.aestronglyMeasurable _,
    (uniformSmallRestrictions_iff_unifIntegrable _).mp
      (uniformSmallRestrictions_packetShadow hp k f hf η hη hb T g),
    ⟨⟨‖T‖ * ‖g‖, mul_nonneg (norm_nonneg _) (norm_nonneg _)⟩, fun i => ?_⟩⟩
  rw [← Lp.enorm_def, ← ofReal_norm_eq_enorm]
  simpa only [ENNReal.ofReal_eq_coe_nnreal (mul_nonneg (norm_nonneg T) (norm_nonneg g))]
    using ENNReal.ofReal_le_ofReal (norm_packetShadow_le k f hf η hη hb T g i)

theorem uniformSmallRestrictions_smul {f : ι → Lp 𝕜 1 unitIntervalMeasure}
    (hf : UniformSmallRestrictions f) (c : 𝕜) :
    UniformSmallRestrictions (fun i => c • f i) := by
  intro ε hε
  have hc : 0 < ‖c‖ + 1 := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := hf (ε / (‖c‖ + 1)) (div_pos hε hc)
  refine ⟨δ, hδ, fun i s hs hμ => ?_⟩
  rw [map_smul, norm_smul]
  have hfrac : ‖c‖ * (ε / (‖c‖ + 1)) < ε := by
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ hc).mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_left (hsmall i s hs hμ) (norm_nonneg c)).trans hfrac.le

end SurveyStatements.P5OperatorReduction
