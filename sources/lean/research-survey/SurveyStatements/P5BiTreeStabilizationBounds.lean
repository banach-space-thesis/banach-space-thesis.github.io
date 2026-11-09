import SurveyStatements.P5BiTreeStabilizationRectangleEstimates

/-! Telescope the genuinely constructed slice and rectangle estimates
to all four bi-tree edge conditions and fixed root values. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem norm_sub_lt_pair {a b c : 𝕜} {u v : ℝ}
    (hab : ‖a - b‖ < u) (hbc : ‖b - c‖ < v) : ‖a - c‖ < u + v := by
  have h : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  exact h.trans_lt (add_lt_add hab hbc)

theorem norm_sub_lt_chain6 {a b c d e f g : 𝕜} {u v w x y z : ℝ}
    (hab : ‖a - b‖ < u) (hbc : ‖b - c‖ < v) (hcd : ‖c - d‖ < w)
    (hde : ‖d - e‖ < x) (hef : ‖e - f‖ < y) (hfg : ‖f - g‖ < z) :
    ‖a - g‖ < u + v + w + x + y + z :=
  norm_sub_lt_pair (norm_sub_lt_pair (norm_sub_lt_pair
    (norm_sub_lt_pair (norm_sub_lt_pair hab hbc) hcd) hde) hef) hfg

theorem exists_dyadic_parent (J : DyadicIndex) (n : ℕ) (hJ : J.1 = n + 1) :
    ∃ K : DyadicIndex, K.1 = n ∧ ∃ b : Bool, J = child K b := by
  rcases J with ⟨m, l⟩
  change m = n + 1 at hJ
  subst m
  obtain ⟨⟨k, b⟩, rfl⟩ := (lpHaarChildrenEquiv n).surjective l
  refine ⟨⟨n, k⟩, rfl, ?_⟩
  fin_cases b
  · refine ⟨true, ?_⟩
    change (⟨n + 1, (lpHaarChildrenEquiv n) (k, 0)⟩ : DyadicIndex) = child ⟨n, k⟩ true
    rw [lpHaarChildrenEquiv_left]
    rfl
  · refine ⟨false, ?_⟩
    change (⟨n + 1, (lpHaarChildrenEquiv n) (k, 1)⟩ : DyadicIndex) = child ⟨n, k⟩ false
    rw [lpHaarChildrenEquiv_right]
    rfl

variable (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
  (ε : ℕ → ℝ) (r : (n : ℕ) → LevelPairs n)
  (hr : ∀ n, RoundSpec d H ε n (fun i : Fin n => r i.val) (r n))

include hr in
theorem lower_edge_bound (I J : DyadicIndex) (hJI : J.1 ≤ I.1) (b : Bool) :
    ‖roundSymbol d r (child I b) J - roundSymbol d r I J‖ <
      ε (I.1 + 1) + ε I.1 + ε I.1 := by
  have h1 := lower_slice_approx d H ε r hr (child I b) J (by simp only [child_level]; omega)
  have h2 := lower_slice_balance d H ε r hr I J hJI b
  have h3 : ‖lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
      (outerParent r I) - roundSymbol d r I J‖ < ε I.1 := by
    simpa only [norm_sub_rev] using lower_slice_approx d H ε r hr I J hJI
  exact norm_sub_lt_pair (norm_sub_lt_pair h1 h2) h3

include hr in
theorem upper_edge_bound (I J : DyadicIndex) (hIJ : I.1 < J.1) (b : Bool) :
    ‖roundSymbol d r I (child J b) - roundSymbol d r I J‖ <
      ε (J.1 + 1) + ε J.1 + ε J.1 := by
  have h1 := upper_slice_approx d H ε r hr I (child J b) (by simp only [child_level]; omega)
  have h2 := upper_slice_balance d H ε r hr I J hIJ b
  have h3 : ‖lpHaarParentTrace (averageTraces H.innerTrace (outerBlock r I)).value
      (innerParent r J) - roundSymbol d r I J‖ < ε J.1 := by
    simpa only [norm_sub_rev] using upper_slice_approx d H ε r hr I J hIJ
  exact norm_sub_lt_pair (norm_sub_lt_pair h1 h2) h3

include hr in
theorem diagonal_edge_bound (I J : DyadicIndex) (hIJ : I.1 = J.1) (b c : Bool) :
    ‖roundSymbol d r (child I b) (child J c) - roundSymbol d r I J‖ <
      ε (I.1 + 1) + ε (I.1 + 1) + ε I.1 + ε I.1 + ε I.1 + ε I.1 := by
  have h1 := lower_slice_approx d H ε r hr (child I b) (child J c)
    (by simp only [child_level]; omega)
  have h2 := lower_diagonal_trace_approx d H ε r hr (child I b) (child J c)
    (by simp only [child_level]; omega)
  have h3 := rectangle_outer_balance d H ε r hr true I J hIJ b c
  have h4 := rectangle_inner_balance d H ε r hr true I J hIJ c
  have h5 : ‖rectangleMean H.lowerTrace (outerParent r I) (innerParent r J) -
      lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value (outerParent r I)‖ <
        ε J.1 := by
    simpa only [norm_sub_rev] using lower_diagonal_trace_approx d H ε r hr I J hIJ
  have h6 : ‖lpHaarParentTrace (averageTraces H.outerTrace (innerBlock r J)).value
      (outerParent r I) - roundSymbol d r I J‖ < ε I.1 := by
    simpa only [norm_sub_rev] using lower_slice_approx d H ε r hr I J hIJ.ge
  simpa only [selectedRectangleTrace, if_true, child_level, ← hIJ] using
    norm_sub_lt_chain6 h1 h2 h3 h4 h5 h6

include hr in
theorem superdiagonal_edge_bound (I K : DyadicIndex) (hIK : I.1 = K.1)
    (c b e : Bool) :
    ‖roundSymbol d r (child I b) (child (child K c) e) - roundSymbol d r I (child K c)‖ <
      ε (I.1 + 2) + ε (I.1 + 1) + ε (I.1 + 1) + ε I.1 + ε I.1 + ε (I.1 + 1) := by
  have h1 := upper_slice_approx d H ε r hr (child I b) (child (child K c) e)
    (by simp only [child_level]; omega)
  have h2 := upper_diagonal_trace_approx d H ε r hr (child I b) (child K c)
    (by simp only [child_level]; omega) e
  have h3 := rectangle_inner_balance d H ε r hr false (child I b) (child K c)
    (by simp only [child_level]; omega) e
  have h4 := rectangle_outer_balance d H ε r hr false I K hIK b c
  have h5 : ‖rectangleMean H.upperTrace (outerParent r I) (innerParent r (child K c)) -
      lpHaarParentTrace (averageTraces H.innerTrace (outerBlock r I)).value
        (innerParent r (child K c))‖ < ε I.1 := by
    simpa only [norm_sub_rev] using upper_diagonal_trace_approx d H ε r hr I K hIK c
  have h6 : ‖lpHaarParentTrace (averageTraces H.innerTrace (outerBlock r I)).value
      (innerParent r (child K c)) - roundSymbol d r I (child K c)‖ < ε (child K c).1 := by
    simpa only [norm_sub_rev] using upper_slice_approx d H ε r hr I (child K c)
      (by simp only [child_level]; omega)
  simpa only [selectedRectangleTrace, Bool.false_eq_true, if_false, child_level,
    ← hIK, Nat.add_assoc] using norm_sub_lt_chain6 h1 h2 h3 h4 h5 h6

include hr in
theorem root_lower_bound :
    ‖roundSymbol d r root root - rectangleMean H.lowerTrace
      LpHaarFiniteParent.root LpHaarFiniteParent.root‖ < ε 0 + ε 0 := by
  have h1 := lower_slice_approx d H ε r hr root root (le_refl _)
  have h2 := lower_diagonal_trace_approx d H ε r hr root root rfl
  have h := norm_sub_lt_pair h1 h2
  have heq : rectangleMean H.lowerTrace (outerParent r root) (innerParent r root) =
      rectangleMean H.lowerTrace LpHaarFiniteParent.root LpHaarFiniteParent.root :=
    rectangle_root_mean d H ε r hr true
  rw [heq] at h
  exact h

include hr in
theorem root_upper_bound (b : Bool) :
    ‖roundSymbol d r root (child root b) - rectangleMean H.upperTrace
      LpHaarFiniteParent.root LpHaarFiniteParent.root‖ < ε 1 + ε 0 + ε 0 := by
  have h1 := upper_slice_approx d H ε r hr root (child root b) (by
    change (0 : ℕ) < 1
    decide)
  have h2 := upper_diagonal_trace_approx d H ε r hr root root rfl b
  have h3 := rectangle_inner_balance d H ε r hr false root root rfl b
  have h := norm_sub_lt_pair (norm_sub_lt_pair h1 h2) h3
  have heq : rectangleMean H.upperTrace (outerParent r root) (innerParent r root) =
      rectangleMean H.upperTrace LpHaarFiniteParent.root LpHaarFiniteParent.root :=
    rectangle_root_mean d H ε r hr false
  simp only [selectedRectangleTrace, Bool.false_eq_true, if_false] at h
  rw [heq] at h
  exact h

end SurveyStatements.P5.BiTree
