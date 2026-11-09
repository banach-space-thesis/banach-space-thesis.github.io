import SurveyStatements.P5GeneralMixedErrorCanonicalCoordinates

/-! Only the genuinely mixed off-diagonal remainder is constructed as a
nuclear series, using its full canonical coordinate and vector norm budget. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_generalMixedCanonicalNuclearError (hp : p ≠ ∞)
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (b : GeneralMixedNuclearIndex → ℝ) (hb : Summable b)
    (hbudget : ∀ q : GeneralMixedNuclearIndex,
      ‖a q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2‖ *
        (‖cancellativeHaarCoordinate 𝕜 p q.val.2.1 q.val.2.2‖ *
          ‖cancellativeHaar 𝕜 p q.val.1.1 q.val.1.2‖) ≤ b q) :
    ∃ E : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      ‖E‖ ≤ ∑' q, b q ∧ ∀ I J K L : DyadicIndex,
        cancellativeHaarCoordinate 𝕜 p I J (E (cancellativeHaar 𝕜 p K L)) =
          if I ≠ K ∧ J ≠ L then a I J K L else 0 := by
  refine ⟨mixedNuclearError (𝕜 := 𝕜) (p := p)
    (fun q : GeneralMixedNuclearIndex => q.val.2)
    (fun q : GeneralMixedNuclearIndex => q.val.1)
    (fun q => a q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2), ?_, ?_⟩
  · exact norm_mixedNuclearError_le _ _ _ b hb hbudget
  · exact mixedNuclearError_canonical_coordinate hp a b hb hbudget

end SurveyStatements.P5
