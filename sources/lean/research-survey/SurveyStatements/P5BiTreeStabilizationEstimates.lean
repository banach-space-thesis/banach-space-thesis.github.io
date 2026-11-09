import SurveyStatements.P5BiTreeStabilizationOrdered

/-! Read the alternating-round estimates at actual dyadic indices. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev outerBlock (r : (n : ℕ) → LevelPairs n) (I : DyadicIndex) := (r I.1).1 I.2
abbrev innerBlock (r : (n : ℕ) → LevelPairs n) (J : DyadicIndex) := (r J.1).2 J.2
abbrev outerParent (r : (n : ℕ) → LevelPairs n) (I : DyadicIndex) := (outerBlock r I).parent
abbrev innerParent (r : (n : ℕ) → LevelPairs n) (J : DyadicIndex) := (innerBlock r J).parent

def roundSymbol (d : DyadicIndex → DyadicIndex → 𝕜)
    (r : (n : ℕ) → LevelPairs n) (I J : DyadicIndex) : 𝕜 :=
  blockAverage d (outerBlock r I) (innerBlock r J)

variable (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
  (ε : ℕ → ℝ) (r : (n : ℕ) → LevelPairs n)
  (hr : ∀ n, RoundSpec d H ε n (fun i : Fin n => r i.val) (r n))

include hr in
theorem outerParent_set (I : DyadicIndex) :
    (outerParent r I).set = (outerParents I.1 (fun i : Fin I.1 => r i.val) I.2).set :=
  ((hr I.1).outer I.2).parent

include hr in
theorem innerParent_set (J : DyadicIndex) :
    (innerParent r J).set = (innerParents J.1 (fun i : Fin J.1 => r i.val) J.2).set :=
  ((hr J.1).inner J.2).parent

include hr in
theorem outerChild_parent (I : DyadicIndex) (b : Bool) :
    (outerParent r (child I b)).set = ((outerBlock r I).child b).set :=
  (roundOuterTree d H ε r hr).children I b

include hr in
theorem innerChild_parent (J : DyadicIndex) (b : Bool) :
    (innerParent r (child J b)).set = ((innerBlock r J).child b).set :=
  (roundInnerTree d H ε r hr).children J b

include hr in
theorem lower_slice_approx (I J : DyadicIndex) (hJI : J.1 ≤ I.1) :
    ‖roundSymbol d r I J -
      lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
        (outerParent r I)‖ < ε I.1 := by
  let index : PastIndex (I.1 + 1) := ⟨⟨J.1, by omega⟩, J.2⟩
  have h := ((hr I.1).outer I.2).past_approx index
  have h' : ‖roundSymbol d r I J -
      lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
        (outerParents I.1 (fun i : Fin I.1 => r i.val) I.2)‖ < ε I.1 := by
    simpa only [index, innerThroughCurrent, extendedInner_sequence] using h
  have hP := lpHaarParentTrace_congr
    (averageTraces H.outerTrace (innerBlock r J)).value
    (averageTraces H.outerTrace (innerBlock r J)).congr _ _
    (outerParent_set d H ε r hr I)
  rw [hP]
  exact h'

include hr in
theorem lower_slice_balance (I J : DyadicIndex) (hJI : J.1 ≤ I.1) (b : Bool) :
    ‖lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
      (outerParent r (child I b)) -
      lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
        (outerParent r I)‖ < ε I.1 := by
  let index : PastIndex (I.1 + 1) := ⟨⟨J.1, by omega⟩, J.2⟩
  have h := ((hr I.1).outer I.2).past_balance index b
  have h' : ‖lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
      ((outerBlock r I).child b) -
      lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
        (outerParents I.1 (fun i : Fin I.1 => r i.val) I.2)‖ < ε I.1 := by
    simpa only [index, innerThroughCurrent, extendedInner_sequence] using h
  have hPc := lpHaarParentTrace_congr
    (averageTraces H.outerTrace (innerBlock r J)).value
    (averageTraces H.outerTrace (innerBlock r J)).congr _ _
    (outerChild_parent d H ε r hr I b)
  have hP := lpHaarParentTrace_congr
    (averageTraces H.outerTrace (innerBlock r J)).value
    (averageTraces H.outerTrace (innerBlock r J)).congr _ _
    (outerParent_set d H ε r hr I)
  rw [hPc, hP]
  exact h'

include hr in
theorem upper_slice_approx (I J : DyadicIndex) (hIJ : I.1 < J.1) :
    ‖roundSymbol d r I J -
      lpHaarParentTrace (averageTraces H.innerTrace (outerBlock r I)).value
        (innerParent r J)‖ < ε J.1 := by
  let index : PastIndex J.1 := ⟨⟨I.1, hIJ⟩, I.2⟩
  have h := ((hr J.1).inner J.2).past_approx index
  have hQ := lpHaarParentTrace_congr
    (averageTraces H.innerTrace (outerBlock r I)).value
    (averageTraces H.innerTrace (outerBlock r I)).congr _ _
    (innerParent_set d H ε r hr J)
  rw [hQ]
  simpa only [index, pastOuter] using h

include hr in
theorem upper_slice_balance (I J : DyadicIndex) (hIJ : I.1 < J.1) (b : Bool) :
    ‖lpHaarParentTrace (averageTraces H.innerTrace (outerBlock r I)).value
      (innerParent r (child J b)) -
      lpHaarParentTrace (averageTraces H.innerTrace (outerBlock r I)).value
        (innerParent r J)‖ < ε J.1 := by
  let index : PastIndex J.1 := ⟨⟨I.1, hIJ⟩, I.2⟩
  have h := ((hr J.1).inner J.2).past_balance index b
  have hQc := lpHaarParentTrace_congr
    (averageTraces H.innerTrace (outerBlock r I)).value
    (averageTraces H.innerTrace (outerBlock r I)).congr _ _
    (innerChild_parent d H ε r hr J b)
  have hQ := lpHaarParentTrace_congr
    (averageTraces H.innerTrace (outerBlock r I)).value
    (averageTraces H.innerTrace (outerBlock r I)).congr _ _
    (innerParent_set d H ε r hr J)
  rw [hQc, hQ]
  simpa only [index, pastOuter] using h

end SurveyStatements.P5.BiTree
