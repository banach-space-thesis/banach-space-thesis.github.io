import SurveyStatements.P5BiTreeStabilizationNormalized
import SurveyStatements.P5BiTreeStabilizationGeometry

/-! Genuine inner and outer choices in one alternating round. Each split
controls all past coefficient slices and both fixed limiting rectangle
traces. Only finitely many constraints are imposed in a round. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem eventually_close_of_limit (f : ℕ → 𝕜) (c : 𝕜)
    (hf : Tendsto f atTop (𝓝 c)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖f n - c‖ < ε := by
  have h : Tendsto (fun n => ‖f n - c‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hf.sub (tendsto_const_nhds (x := c))).norm
  exact (tendsto_order.mp h).2 ε hε

theorem finite_trace_parent_select {A : Type*} [Fintype A] {M : ℝ}
    (hM : 0 ≤ M) (a : A → DyadicTrace 𝕜 M)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (Good : ℕ → Prop) (hgood : ∀ᶠ n in atTop, Good (levels n))
    (P : LpHaarFiniteParent) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧ Good S.level ∧
      ∀ r b, ‖lpHaarParentTrace (a r).value (S.child b) -
        lpHaarParentTrace (a r).value P‖ < ε := by
  let e := Fintype.equivFin A
  obtain ⟨S, hN, hP, hG, hs⟩ := simultaneous_trace_parent_select hM
    (fun i => a (e.symm i)) levels hlevels Good hgood P N hε
  refine ⟨S, hN, hP, hG, fun r b => ?_⟩
  simpa only [Equiv.symm_apply_apply] using hs (e r) b

theorem averageTrace_eq_splitDiagonal {M : ℝ}
    (a : DyadicIndex → DyadicTrace 𝕜 M) (S : LpHaarFiniteSplit)
    (P : LpHaarFiniteParent) :
    lpHaarParentTrace (averageTraces a S).value P =
      lpHaarSplitDiagonal (fun l k => (a ⟨l, k⟩).value P.index) S /
        ((volume.restrict (Icc (0 : ℝ) 1)).real P.set : 𝕜) := rfl

theorem blockAverage_eq_splitDiagonal (d : DyadicIndex → DyadicIndex → 𝕜)
    (S T : LpHaarFiniteSplit) : blockAverage d S T =
      lpHaarSplitDiagonal (fun l k => finiteAverage T.atoms
        (fun j => d ⟨l, k⟩ ⟨T.level, j⟩)) S :=
  blockAverage_eq_average d S T

theorem blockAverage_flip (d : DyadicIndex → DyadicIndex → 𝕜)
    (S T : LpHaarFiniteSplit) :
    blockAverage (fun I J => d J I) T S = blockAverage d S T := by
  unfold blockAverage
  rw [Finset.sum_comm]
  ring

structure InnerStepSpec {A B : Type*} [Fintype A] [Fintype B]
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
    (parents : A → LpHaarFiniteParent) (past : B → LpHaarFiniteSplit)
    (Q : LpHaarFiniteParent) (N : ℕ) (ε : ℝ) (T : LpHaarFiniteSplit) : Prop where
  level : N ≤ T.level
  parent : T.parent.set = Q.set
  past_approx : ∀ r, ‖blockAverage d (past r) T -
    lpHaarParentTrace (averageTraces H.innerTrace (past r)).value Q‖ < ε
  lower_approx : ∀ r, ‖lpHaarParentTrace (averageTraces H.outerTrace T).value (parents r) -
    rectangleMean H.lowerTrace (parents r) Q‖ < ε
  past_balance : ∀ r b, ‖lpHaarParentTrace (averageTraces H.innerTrace (past r)).value
    (T.child b) - lpHaarParentTrace (averageTraces H.innerTrace (past r)).value Q‖ < ε
  lower_balance : ∀ r b, ‖rectangleMean H.lowerTrace (parents r) (T.child b) -
    rectangleMean H.lowerTrace (parents r) Q‖ < ε
  upper_balance : ∀ r b, ‖rectangleMean H.upperTrace (parents r) (T.child b) -
    rectangleMean H.upperTrace (parents r) Q‖ < ε

theorem exists_inner_step {A B : Type*} [Fintype A] [Fintype B]
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (H : IteratedTraceData d M) (parents : A → LpHaarFiniteParent)
    (past : B → LpHaarFiniteSplit) (Q : LpHaarFiniteParent) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : LpHaarFiniteSplit, InnerStepSpec d H parents past Q N ε T := by
  let traces : B ⊕ (A ⊕ A) → DyadicTrace 𝕜 M := Sum.elim
    (fun r => averageTraces H.innerTrace (past r))
    (Sum.elim (fun r => H.lowerTrace.normalizedRightSlice (parents r))
      (fun r => H.upperTrace.normalizedRightSlice (parents r)))
  let Good (n : ℕ) : Prop :=
    (∀ r, ‖levelMean (fun l k => finiteAverage (past r).atoms
      (fun i => d ⟨(past r).level, i⟩ ⟨l, k⟩)) n Q -
        lpHaarParentTrace (averageTraces H.innerTrace (past r)).value Q‖ < ε) ∧
    ∀ r, ‖levelMean (fun l k => (H.outerTrace ⟨l, k⟩).value (parents r).index) n Q /
      ((volume.restrict (Icc (0 : ℝ) 1)).real (parents r).set : 𝕜) -
        rectangleMean H.lowerTrace (parents r) Q‖ < ε
  have hgood : ∀ᶠ n in atTop, Good (H.innerLevels n) := by
    have hpast : ∀ᶠ n in atTop, ∀ r : B, _ := eventually_all.mpr (fun r =>
      levelMean_eventually_close _ _ H.innerLevels
        (H.inner_block_limit d (past r)) Q hε)
    have hlower : ∀ᶠ n in atTop, ∀ r : A, _ := eventually_all.mpr (fun r =>
      eventually_close_of_limit _ _ (H.lower_rectangle_limit d (parents r) Q) hε)
    exact hpast.and hlower
  obtain ⟨T, hN, hQ, hG, hb⟩ := finite_trace_parent_select hM traces
    H.innerLevels H.innerLevels_strict Good hgood Q N hε
  refine ⟨T, ⟨hN, hQ, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r
    have h := hG.1 r
    rw [← blockAverage_flip d (past r) T, blockAverage_eq_splitDiagonal,
      splitDiagonal_eq_levelMean]
    simpa only [levelMean, hQ] using h
  · intro r
    rw [averageTrace_eq_splitDiagonal, splitDiagonal_eq_levelMean]
    simpa only [levelMean, hQ] using hG.2 r
  · intro r b
    exact hb (Sum.inl r) b
  · intro r b
    have h := hb (Sum.inr (Sum.inl r)) b
    change ‖lpHaarParentTrace (H.lowerTrace.normalizedRightSlice (parents r)).value
      (T.child b) - lpHaarParentTrace (H.lowerTrace.normalizedRightSlice (parents r)).value Q‖ < ε at h
    simpa only [parentTrace_normalizedRightSlice] using h
  · intro r b
    have h := hb (Sum.inr (Sum.inr r)) b
    change ‖lpHaarParentTrace (H.upperTrace.normalizedRightSlice (parents r)).value
      (T.child b) - lpHaarParentTrace (H.upperTrace.normalizedRightSlice (parents r)).value Q‖ < ε at h
    simpa only [parentTrace_normalizedRightSlice] using h

structure OuterStepSpec {A B : Type*} [Fintype A] [Fintype B]
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
    (children : A → LpHaarFiniteParent) (inner : B → LpHaarFiniteSplit)
    (P : LpHaarFiniteParent) (N : ℕ) (ε : ℝ) (S : LpHaarFiniteSplit) : Prop where
  level : N ≤ S.level
  parent : S.parent.set = P.set
  past_approx : ∀ r, ‖blockAverage d S (inner r) -
    lpHaarParentTrace (averageTraces H.outerTrace (inner r)).value P‖ < ε
  upper_approx : ∀ r, ‖lpHaarParentTrace (averageTraces H.innerTrace S).value (children r) -
    rectangleMean H.upperTrace P (children r)‖ < ε
  past_balance : ∀ r b, ‖lpHaarParentTrace (averageTraces H.outerTrace (inner r)).value
    (S.child b) - lpHaarParentTrace (averageTraces H.outerTrace (inner r)).value P‖ < ε
  lower_balance : ∀ r b, ‖rectangleMean H.lowerTrace (S.child b) (children r) -
    rectangleMean H.lowerTrace P (children r)‖ < ε
  upper_balance : ∀ r b, ‖rectangleMean H.upperTrace (S.child b) (children r) -
    rectangleMean H.upperTrace P (children r)‖ < ε

theorem exists_outer_step {A B : Type*} [Fintype A] [Fintype B]
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (H : IteratedTraceData d M) (children : A → LpHaarFiniteParent)
    (inner : B → LpHaarFiniteSplit) (P : LpHaarFiniteParent) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : LpHaarFiniteSplit, OuterStepSpec d H children inner P N ε S := by
  let traces : B ⊕ (A ⊕ A) → DyadicTrace 𝕜 M := Sum.elim
    (fun r => averageTraces H.outerTrace (inner r))
    (Sum.elim (fun r => H.lowerTrace.normalizedLeftSlice (children r))
      (fun r => H.upperTrace.normalizedLeftSlice (children r)))
  let Good (n : ℕ) : Prop :=
    (∀ r, ‖levelMean (fun l k => finiteAverage (inner r).atoms
      (fun j => d ⟨l, k⟩ ⟨(inner r).level, j⟩)) n P -
        lpHaarParentTrace (averageTraces H.outerTrace (inner r)).value P‖ < ε) ∧
    ∀ r, ‖levelMean (fun l k => (H.innerTrace ⟨l, k⟩).value (children r).index) n P /
      ((volume.restrict (Icc (0 : ℝ) 1)).real (children r).set : 𝕜) -
        rectangleMean H.upperTrace P (children r)‖ < ε
  have hgood : ∀ᶠ n in atTop, Good (H.outerLevels n) := by
    have hpast : ∀ᶠ n in atTop, ∀ r : B, _ := eventually_all.mpr (fun r =>
      levelMean_eventually_close _ _ H.outerLevels
        (H.outer_block_limit d (inner r)) P hε)
    have hupper : ∀ᶠ n in atTop, ∀ r : A, _ := eventually_all.mpr (fun r =>
      eventually_close_of_limit _ _ (H.upper_rectangle_limit d P (children r)) hε)
    exact hpast.and hupper
  obtain ⟨S, hN, hP, hG, hb⟩ := finite_trace_parent_select hM traces
    H.outerLevels H.outerLevels_strict Good hgood P N hε
  refine ⟨S, ⟨hN, hP, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r
    rw [blockAverage_eq_splitDiagonal, splitDiagonal_eq_levelMean]
    simpa only [levelMean, hP] using hG.1 r
  · intro r
    rw [averageTrace_eq_splitDiagonal, splitDiagonal_eq_levelMean]
    simpa only [levelMean, hP] using hG.2 r
  · intro r b
    exact hb (Sum.inl r) b
  · intro r b
    have h := hb (Sum.inr (Sum.inl r)) b
    change ‖lpHaarParentTrace (H.lowerTrace.normalizedLeftSlice (children r)).value
      (S.child b) - lpHaarParentTrace (H.lowerTrace.normalizedLeftSlice (children r)).value P‖ < ε at h
    simpa only [parentTrace_normalizedLeftSlice] using h
  · intro r b
    have h := hb (Sum.inr (Sum.inr r)) b
    change ‖lpHaarParentTrace (H.upperTrace.normalizedLeftSlice (children r)).value
      (S.child b) - lpHaarParentTrace (H.upperTrace.normalizedLeftSlice (children r)).value P‖ < ε at h
    simpa only [parentTrace_normalizedLeftSlice] using h

end SurveyStatements.P5.BiTree
