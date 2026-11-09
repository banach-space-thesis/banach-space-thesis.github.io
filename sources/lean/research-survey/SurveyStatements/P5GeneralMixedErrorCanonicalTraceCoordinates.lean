import SurveyStatements.P5GeneralMixedErrorCanonicalCoordinates

/-! The actual balanced-trace strip series have precisely the desired
canonical matrix entries when their heap symbols are the compressed entries. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem generalMixed_outer_trace_coordinates_of_heap_coefficients
    (E : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (g : GeneralMixedStripIndex → ℕ → 𝕜)
    (hE : ∀ A B I R : DyadicIndex,
      cancellativeHaarCoordinate 𝕜 p A B (E (cancellativeHaar 𝕜 p I R)) =
        ∑' q : GeneralMixedStripIndex, if q.val.2 = R then
          g q (lpHaarHeapIndex I.1 I.2) *
            (if (A, B) = (I, q.val.1) then 1 else 0) else 0)
    (hcoeff : ∀ q : GeneralMixedStripIndex, ∀ I : DyadicIndex,
      g q (lpHaarHeapIndex I.1 I.2) = a I q.val.1 I q.val.2)
    (A B I R : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p A B (E (cancellativeHaar 𝕜 p I R)) =
      if A = I ∧ B ≠ R then a I B I R else 0 := by
  rw [hE]
  calc
    _ = ∑' q : GeneralMixedStripIndex, if q.val.2 = R then
        a I q.val.1 I q.val.2 *
          (if (A, B) = (I, q.val.1) then 1 else 0) else 0 := by
      apply tsum_congr
      intro q
      rw [hcoeff q I]
    _ = _ := generalMixed_outer_strip_matrix_sum a A B I R

theorem generalMixed_inner_trace_coordinates_of_heap_coefficients
    (E : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (g : GeneralMixedStripIndex → ℕ → 𝕜)
    (hE : ∀ A B L J : DyadicIndex,
      cancellativeHaarCoordinate 𝕜 p A B (E (cancellativeHaar 𝕜 p L J)) =
        ∑' q : GeneralMixedStripIndex, if q.val.2 = L then
          g q (lpHaarHeapIndex J.1 J.2) *
            (if (A, B) = (q.val.1, J) then 1 else 0) else 0)
    (hcoeff : ∀ q : GeneralMixedStripIndex, ∀ J : DyadicIndex,
      g q (lpHaarHeapIndex J.1 J.2) = a q.val.1 J q.val.2 J)
    (A B L J : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p A B (E (cancellativeHaar 𝕜 p L J)) =
      if A ≠ L ∧ B = J then a A J L J else 0 := by
  rw [hE]
  calc
    _ = ∑' q : GeneralMixedStripIndex, if q.val.2 = L then
        a q.val.1 J q.val.2 J *
          (if (A, B) = (q.val.1, J) then 1 else 0) else 0 := by
      apply tsum_congr
      intro q
      rw [hcoeff q J]
    _ = _ := generalMixed_inner_strip_matrix_sum a A B L J

end SurveyStatements.P5
