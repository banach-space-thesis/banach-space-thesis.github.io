import SurveyStatements.P5GeneralMixedErrorOperators

/-! Off-diagonal errors are assembled as actual bounded operators before
identifying the diagonal remainder. The hypotheses record genuine operator
budgets and exact coordinates; construction of those errors is separate. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem generalMixed_cancellative_coordinates_separate (hp : p ≠ ∞)
    (x y : DoublyZeroMean 𝕜 p)
    (hxy : ∀ I J, cancellativeHaarCoordinate 𝕜 p I J x =
      cancellativeHaarCoordinate 𝕜 p I J y) : x = y := by
  apply Subtype.ext
  exact productHaarCoordinates_separate hp x.val y.val x.property y.property hxy

def generalMixedDiagonalRemainder
    (U Eouter Einner Emixed : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) :
    DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  U - Eouter - Einner - Emixed

theorem generalMixedDiagonalRemainder_multiplier (hp : p ≠ ∞)
    (U Eouter Einner Emixed : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜)
    (hcoordinates : ∀ I J K L,
      cancellativeHaarCoordinate 𝕜 p I J (U (cancellativeHaar 𝕜 p K L)) =
        cancellativeHaarCoordinate 𝕜 p I J
          (d K L • cancellativeHaar 𝕜 p K L +
            Eouter (cancellativeHaar 𝕜 p K L) +
            Einner (cancellativeHaar 𝕜 p K L) +
            Emixed (cancellativeHaar 𝕜 p K L))) :
    IsProductHaarMultiplier (generalMixedDiagonalRemainder U Eouter Einner Emixed) d := by
  intro K L
  apply generalMixed_cancellative_coordinates_separate (𝕜 := 𝕜) (p := p) hp
  intro I J
  simp only [generalMixedDiagonalRemainder, ContinuousLinearMap.sub_apply, map_sub,
    map_add] at hcoordinates ⊢
  rw [hcoordinates I J K L]
  abel

theorem norm_generalMixedDiagonalRemainder_error_le
    (U Eouter Einner Emixed : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (Couter Cinner Cmixed : ℝ)
    (ho : ‖Eouter‖ ≤ Couter) (hi : ‖Einner‖ ≤ Cinner) (hm : ‖Emixed‖ ≤ Cmixed) :
    ‖U - generalMixedDiagonalRemainder U Eouter Einner Emixed‖ ≤
      Couter + Cinner + Cmixed := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have heq : U - generalMixedDiagonalRemainder U Eouter Einner Emixed =
      Eouter + Einner + Emixed := by
    dsimp only [generalMixedDiagonalRemainder]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ho hi)) hm)

theorem exists_generalMixed_multiplier_of_error_coordinates (hp : p ≠ ∞)
    (U Eouter Einner Emixed : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (Couter Cinner Cmixed : ℝ)
    (ho : ‖Eouter‖ ≤ Couter) (hi : ‖Einner‖ ≤ Cinner) (hm : ‖Emixed‖ ≤ Cmixed)
    (hcoordinates : ∀ I J K L,
      cancellativeHaarCoordinate 𝕜 p I J (U (cancellativeHaar 𝕜 p K L)) =
        cancellativeHaarCoordinate 𝕜 p I J
          (d K L • cancellativeHaar 𝕜 p K L +
            Eouter (cancellativeHaar 𝕜 p K L) +
            Einner (cancellativeHaar 𝕜 p K L) +
            Emixed (cancellativeHaar 𝕜 p K L))) :
    ∃ M : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      IsProductHaarMultiplier M d ∧ ‖U - M‖ ≤ Couter + Cinner + Cmixed := by
  exact ⟨generalMixedDiagonalRemainder U Eouter Einner Emixed,
    generalMixedDiagonalRemainder_multiplier (𝕜 := 𝕜) (p := p)
      hp U Eouter Einner Emixed d hcoordinates,
    norm_generalMixedDiagonalRemainder_error_le (𝕜 := 𝕜) (p := p) U Eouter Einner Emixed
      Couter Cinner Cmixed ho hi hm⟩

end SurveyStatements.P5
