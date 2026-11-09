import SurveyStatements.P5HaarDiagonalBounds
import SurveyStatements.P5Support.LpHaarTraceLimit

/-! Simultaneous subsequential inner diagonal traces for actual mixed-space
operators. This asserts a common subsequence; it does not assert convergence
of the full sequence in the paper's local L1 trace theorem. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace SurveyStatements.P5

attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def cancellativeHaarDiagonal
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (I J : DyadicIndex) : 𝕜 :=
  cancellativeHaarCoordinate 𝕜 p I J (T (cancellativeHaar 𝕜 p I J))

def innerHaarLevelTrace
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (I : DyadicIndex) (n : ℕ) (s : Set ℝ) : 𝕜 :=
  P5Support.lpHaarLevelTrace (fun l k => cancellativeHaarDiagonal T I ⟨l, k⟩) n s

theorem innerHaarLevelTrace_norm_le (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (I : DyadicIndex) (n : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    ‖innerHaarLevelTrace T I n s‖ ≤ (36 * ‖T‖) * unitIntervalMeasure.real s :=
  P5Support.lpHaarLevelTrace_norm_le _ (by positivity)
    (fun l k => cancellativeHaar_operator_diagonal_norm_le 𝕜 p hp T I ⟨l, k⟩) n s hs

theorem innerHaarLevelTrace_union
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (I : DyadicIndex) (n : ℕ) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) :
    innerHaarLevelTrace T I n (s ∪ t) =
      innerHaarLevelTrace T I n s + innerHaarLevelTrace T I n t :=
  P5Support.lpHaarLevelTrace_union _ n s t hs ht hd

theorem innerHaar_diagonal_subsequence_trace (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) :
    ∃ a : DyadicIndex → P5Support.LpHaarDyadicSetIndex → 𝕜,
      ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ I i, ‖a I i‖ ≤ (36 * ‖T‖) *
        unitIntervalMeasure.real (P5Support.lpHaarDyadicSet i)) ∧
      (∀ I i, Tendsto (fun n => innerHaarLevelTrace T I (r n)
        (P5Support.lpHaarDyadicSet i)) atTop (𝓝 (a I i))) ∧
      (∀ I i j, P5Support.lpHaarDyadicSet i = P5Support.lpHaarDyadicSet j →
        a I i = a I j) ∧
      ∀ I i j k, Disjoint (P5Support.lpHaarDyadicSet i) (P5Support.lpHaarDyadicSet j) →
        P5Support.lpHaarDyadicSet k =
          P5Support.lpHaarDyadicSet i ∪ P5Support.lpHaarDyadicSet j →
        a I k = a I i + a I j := by
  let v (n : ℕ) (i : DyadicIndex × P5Support.LpHaarDyadicSetIndex) : 𝕜 :=
    innerHaarLevelTrace T i.1 n (P5Support.lpHaarDyadicSet i.2)
  have hv (n : ℕ) (i : DyadicIndex × P5Support.LpHaarDyadicSetIndex) :
      ‖v n i‖ ≤ 36 * ‖T‖ := by
    have h := innerHaarLevelTrace_norm_le hp T i.1 n
      (P5Support.lpHaarDyadicSet i.2) (P5Support.lpHaarDyadicSet_measurable i.2)
    have hm : unitIntervalMeasure.real (P5Support.lpHaarDyadicSet i.2) ≤ 1 := by
      simpa using (measureReal_mono (μ := unitIntervalMeasure)
        (subset_univ (P5Support.lpHaarDyadicSet i.2)))
    exact h.trans (by nlinarith [norm_nonneg T])
  obtain ⟨a, r, hr, _, ha⟩ := P5Support.haar_countable_trace_cluster v hv
  refine ⟨fun I i => a (I, i), r, hr, ?_, ?_, ?_, ?_⟩
  · intro I i
    exact le_of_tendsto (ha (I, i)).norm (Eventually.of_forall
      (fun n => innerHaarLevelTrace_norm_le hp T I (r n)
        (P5Support.lpHaarDyadicSet i) (P5Support.lpHaarDyadicSet_measurable i)))
  · intro I i
    exact ha (I, i)
  · intro I i j hij
    apply tendsto_nhds_unique (ha (I, i))
    simpa only [v, hij] using ha (I, j)
  · intro I i j k hdis hunion
    apply tendsto_nhds_unique (ha (I, k))
    convert (ha (I, i)).add (ha (I, j)) using 1
    funext n
    change innerHaarLevelTrace T I (r n) (P5Support.lpHaarDyadicSet k) = _
    rw [hunion, innerHaarLevelTrace_union T I (r n) _ _
      (P5Support.lpHaarDyadicSet_measurable i)
      (P5Support.lpHaarDyadicSet_measurable j) hdis]

end SurveyStatements.P5
