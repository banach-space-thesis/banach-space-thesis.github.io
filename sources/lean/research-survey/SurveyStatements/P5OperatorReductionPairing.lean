import SurveyStatements.P5OperatorReductionReaderSigns
import SurveyStatements.P5HaarNorm

/-! Finite averaging and the actual mixed-space signed pairing bound.
These statements apply to arbitrary bounded mixed operators and actual
scalar Lp inputs. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
open SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def vectorMean {Ω E : Type*} [Fintype Ω] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (v : Ω → E) : E :=
  (((Fintype.card Ω : ℝ)⁻¹ : ℝ) : 𝕜) • ∑ ω, v ω

theorem real_pairing_vectorMean {Ω E : Type*} [Fintype Ω]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (π : E →L[𝕜] 𝕜) (v : Ω → E) :
    RCLike.re (π (vectorMean (𝕜 := 𝕜) v)) = mean (fun ω => RCLike.re (π (v ω))) := by
  simp only [vectorMean, map_smul, map_sum, smul_eq_mul, RCLike.re_ofReal_mul, mean]

theorem exists_mean_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    ∃ ω, mean f ≤ f ω := by
  by_contra h
  push_neg at h
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Ω))
    (fun ω _ => h ω)
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have heq : (∑ ω : Ω, mean f) = ∑ ω : Ω, f ω := by
    simp [mean, hc]
  exact (lt_irrefl _ (hs.trans_eq heq)).elim

theorem norm_mixed_diagonal_pairing_le {n : ℕ}
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (g : Lp 𝕜 1 unitIntervalMeasure)
    (π : Fin n → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜)
    (hπ : ∀ y, ∑ i, ‖π i y‖ ≤ ‖y‖)
    (η : Fin n → ℝ → 𝕜) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1)
    (f : Fin n → Lp 𝕜 p unitIntervalMeasure) :
    ‖∑ i, π i (weightedOuterReader (η i) (hη i) (hb i) (T (tensorWith g (f i))))‖ ≤
      ‖T‖ * ‖g‖ * mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (f i)‖) := by
  let A (i : Fin n) : MixedNorm 𝕜 p →L[𝕜] 𝕜 :=
    (π i).comp (weightedOuterReader (p := p) (η i) (hη i) (hb i))
  have hsum (θ : Fin n → Bool) :
      (∑ i, signedValue (θ i) (T (tensorWith g (f i)))) =
        T (tensorWith g (∑ i, signedValue (θ i) (f i))) := by
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_signedValue, map_signedValue]
  calc
    _ ≤ (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
        ∑ θ : Fin n → Bool, ‖(∑ i, signedValue (θ i) (A i))
          (∑ j, signedValue (θ j) (T (tensorWith g (f j))))‖ :=
      norm_diagonal_sum_le_signed_reader_input_average A (fun i => T (tensorWith g (f i)))
    _ ≤ mean (fun θ : Fin n → Bool =>
        ‖T‖ * ‖g‖ * ‖∑ i, signedValue (θ i) (f i)‖) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
      intro θ _
      rw [hsum]
      calc
        _ ≤ ‖∑ i, signedValue (θ i) (A i)‖ *
            ‖T (tensorWith g (∑ i, signedValue (θ i) (f i)))‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖T (tensorWith g (∑ i, signedValue (θ i) (f i)))‖ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (norm_signed_reader_sum_le π hπ η hη hb θ) (norm_nonneg _)
        _ ≤ ‖T‖ * ‖tensorWith g (∑ i, signedValue (θ i) (f i))‖ := T.le_opNorm _
        _ = _ := by rw [norm_tensorWith]; ring
    _ = _ := mean_mul_left (‖T‖ * ‖g‖) _

end SurveyStatements.P5OperatorReduction
