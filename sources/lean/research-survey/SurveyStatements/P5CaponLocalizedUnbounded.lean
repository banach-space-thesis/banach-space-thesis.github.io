import SurveyStatements.P5CaponLocalizedImages
import SurveyStatements.P5HaarDiagonalBounds

/-! No bounded real operator agrees with Capon on any square dyadic patch. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open P5Support
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem no_real_localized_capon_operator (hp_finite : p ≠ ∞)
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p) :
    ¬ IsLocalizedCaponOperator m i₀ j₀ T := by
  intro hT
  have hlower (N : ℕ) : intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4 ≤
      ‖T (caponLocalizedInput m i₀ j₀ p N)‖ := by
    rw [IsLocalizedCaponOperator.input_image m i₀ j₀ hT]
    exact norm_caponLocalizedImage_lower m i₀ j₀ N
  have hlim : Tendsto (fun N => ‖T (caponLocalizedInput m i₀ j₀ p N)‖) atTop (nhds 0) := by
    simpa using (T.continuous.tendsto 0 |>.comp (tendsto_caponLocalizedInput hp_finite m i₀ j₀)).norm
  have hbad := ge_of_tendsto hlim (Eventually.of_forall hlower)
  have hpos : 0 < intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4 := by
    exact div_pos (mul_pos (intervalLpDyadicRadius_pos m) (intervalLpDyadicRadius_pos m)) (by norm_num)
  exact (not_le_of_gt hpos) hbad

theorem no_real_localized_cancellative_capon_operator (hp_finite : p ≠ ∞)
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (T : DoublyZeroMean ℝ p →L[ℝ] DoublyZeroMean ℝ p) :
    ¬ (∀ I J : DyadicIndex, m ≤ I.1 → lpHaarCell I.1 I.2 ⊆ lpHaarCell m i₀ →
      m ≤ J.1 → lpHaarCell J.1 J.2 ⊆ lpHaarCell m j₀ →
        T (cancellativeHaar ℝ p I J) =
          if J.1 ≤ I.1 then cancellativeHaar ℝ p I J else 0) := by
  intro hT
  let S : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p :=
    (DoublyZeroMean ℝ p).subtypeL.comp (T.comp (cancellativeProjection ℝ p))
  apply no_real_localized_capon_operator hp_finite m i₀ j₀ S
  intro I J hI hIsub hJ hJsub
  have hfix : cancellativeProjection ℝ p (productHaar ℝ p I J) =
      cancellativeHaar ℝ p I J :=
    congrArg (fun L : DoublyZeroMean ℝ p →L[ℝ] DoublyZeroMean ℝ p =>
      L (cancellativeHaar ℝ p I J)) (cancellativeProjection_retraction ℝ p)
  change (T (cancellativeProjection ℝ p (productHaar ℝ p I J))).val = _
  rw [hfix, hT I J hI hIsub hJ hJsub]
  split <;> rfl

end SurveyStatements.P5
