import SurveyStatements.P5CaponImages
import SurveyStatements.P5HaarDiagonalBounds

/-! No bounded real operator on the actual mixed Bochner space, or on its
doubly cancellative subspace, can have Capon's product-Haar values. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem no_real_capon_operator (hp_finite : p ≠ ∞)
    (T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p) : ¬ IsCaponOperator T := by
  intro hT
  have hlower (N : ℕ) : (1 / 4 : ℝ) ≤ ‖T (caponInput p N)‖ := by
    calc
      _ ≤ caponRingReader p (N + 1) (T (caponInput p N)) := hT.ring_reader_input_lower N
      _ ≤ ‖caponRingReader p (N + 1) (T (caponInput p N))‖ := le_abs_self _
      _ ≤ ‖caponRingReader p (N + 1)‖ * ‖T (caponInput p N)‖ :=
        (caponRingReader p (N + 1)).le_opNorm _
      _ ≤ ‖T (caponInput p N)‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (norm_caponRingReader_le _) (norm_nonneg _)
  have hlim : Tendsto (fun N => ‖T (caponInput p N)‖) atTop (nhds 0) := by
    simpa using (T.continuous.tendsto 0 |>.comp (tendsto_caponInput hp_finite)).norm
  have hbad := ge_of_tendsto hlim (Eventually.of_forall hlower)
  norm_num at hbad

theorem no_real_cancellative_capon_operator (hp_finite : p ≠ ∞)
    (T : DoublyZeroMean ℝ p →L[ℝ] DoublyZeroMean ℝ p) :
    ¬ (∀ I J, T (cancellativeHaar ℝ p I J) =
      if J.1 ≤ I.1 then cancellativeHaar ℝ p I J else 0) := by
  intro hT
  let S : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p :=
    (DoublyZeroMean ℝ p).subtypeL.comp (T.comp (cancellativeProjection ℝ p))
  apply no_real_capon_operator hp_finite S
  intro I J
  have hfix : cancellativeProjection ℝ p (productHaar ℝ p I J) =
      cancellativeHaar ℝ p I J := by
    exact congrArg (fun L : DoublyZeroMean ℝ p →L[ℝ] DoublyZeroMean ℝ p =>
      L (cancellativeHaar ℝ p I J)) (cancellativeProjection_retraction ℝ p)
  change (T (cancellativeProjection ℝ p (productHaar ℝ p I J))).val = _
  rw [hfix, hT]
  split <;> rfl

end SurveyStatements.P5
