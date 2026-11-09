import SurveyStatements.P5BiTreeStabilizationEstimates

/-! The alternating signs control both limiting rectangle traces on the
diagonal and the superdiagonal, with the same traces for every budget. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem rectangleMean_congr {M : ℝ} (a : DyadicBiTrace 𝕜 M)
    (P R Q S : LpHaarFiniteParent) (hP : P.set = R.set) (hQ : Q.set = S.set) :
    rectangleMean a P Q = rectangleMean a R S :=
  (rectangleMean_congr_left a P R Q hP).trans (rectangleMean_congr_right a R Q S hQ)

def selectedRectangleTrace (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (H : IteratedTraceData d M) (lower : Bool) : DyadicBiTrace 𝕜 M :=
  if lower then H.lowerTrace else H.upperTrace

variable (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
  (ε : ℕ → ℝ) (r : (n : ℕ) → LevelPairs n)
  (hr : ∀ n, RoundSpec d H ε n (fun i : Fin n => r i.val) (r n))

include hr in
theorem rectangle_inner_balance (lower : Bool) (I J : DyadicIndex)
    (hIJ : I.1 = J.1) (b : Bool) :
    ‖rectangleMean (selectedRectangleTrace d H lower)
      (outerParent r I) (innerParent r (child J b)) -
      rectangleMean (selectedRectangleTrace d H lower)
        (outerParent r I) (innerParent r J)‖ < ε J.1 := by
  rcases I with ⟨n, k⟩
  rcases J with ⟨m, l⟩
  change n = m at hIJ
  subst m
  have hP := outerParent_set d H ε r hr ⟨n, k⟩
  have hQ := innerParent_set d H ε r hr ⟨n, l⟩
  have hQc := innerChild_parent d H ε r hr ⟨n, l⟩ b
  rw [rectangleMean_congr _ _ _ _ _ hP hQc,
    rectangleMean_congr _ _ _ _ _ hP hQ]
  cases lower
  · exact ((hr n).inner l).upper_balance k b
  · exact ((hr n).inner l).lower_balance k b

include hr in
theorem rectangle_outer_balance (lower : Bool) (I J : DyadicIndex)
    (hIJ : I.1 = J.1) (b c : Bool) :
    ‖rectangleMean (selectedRectangleTrace d H lower)
      (outerParent r (child I b)) (innerParent r (child J c)) -
      rectangleMean (selectedRectangleTrace d H lower)
        (outerParent r I) (innerParent r (child J c))‖ < ε I.1 := by
  rcases I with ⟨n, k⟩
  rcases J with ⟨m, l⟩
  change n = m at hIJ
  subst m
  have hP := outerParent_set d H ε r hr ⟨n, k⟩
  have hPc := outerChild_parent d H ε r hr ⟨n, k⟩ b
  have hQc := innerChild_parent d H ε r hr ⟨n, l⟩ c
  rw [rectangleMean_congr _ _ _ _ _ hPc hQc,
    rectangleMean_congr _ _ _ _ _ hP hQc]
  cases lower
  · exact ((hr n).outer k).upper_balance (l, c) b
  · exact ((hr n).outer k).lower_balance (l, c) b

include hr in
theorem lower_diagonal_trace_approx (I J : DyadicIndex) (hIJ : I.1 = J.1) :
    ‖lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
      (outerParent r I) - rectangleMean H.lowerTrace (outerParent r I) (innerParent r J)‖ < ε J.1 := by
  rcases I with ⟨n, k⟩
  rcases J with ⟨m, l⟩
  change n = m at hIJ
  subst m
  have hP := outerParent_set d H ε r hr ⟨n, k⟩
  have hQ := innerParent_set d H ε r hr ⟨n, l⟩
  rw [lpHaarParentTrace_congr _ (averageTraces H.outerTrace (innerBlock r ⟨n, l⟩)).congr
      _ _ hP, rectangleMean_congr _ _ _ _ _ hP hQ]
  exact ((hr n).inner l).lower_approx k

include hr in
theorem upper_diagonal_trace_approx (I J : DyadicIndex) (hIJ : I.1 = J.1) (b : Bool) :
    ‖lpHaarParentTrace (averageTraces H.innerTrace (outerBlock r I)).value
      (innerParent r (child J b)) -
      rectangleMean H.upperTrace (outerParent r I) (innerParent r (child J b))‖ < ε I.1 := by
  rcases I with ⟨n, k⟩
  rcases J with ⟨m, l⟩
  change n = m at hIJ
  subst m
  have hP := outerParent_set d H ε r hr ⟨n, k⟩
  have hQc := innerChild_parent d H ε r hr ⟨n, l⟩ b
  rw [lpHaarParentTrace_congr _ (averageTraces H.innerTrace (outerBlock r ⟨n, k⟩)).congr
      _ _ hQc, rectangleMean_congr _ _ _ _ _ hP hQc]
  exact ((hr n).outer k).upper_approx (l, b)

include hr in
theorem rectangle_root_mean (lower : Bool) :
    rectangleMean (selectedRectangleTrace d H lower) (outerParent r root) (innerParent r root) =
      rectangleMean (selectedRectangleTrace d H lower) LpHaarFiniteParent.root LpHaarFiniteParent.root :=
  rectangleMean_congr _ _ _ _ _ (roundOuterTree d H ε r hr).root
    (roundInnerTree d H ε r hr).root

end SurveyStatements.P5.BiTree
