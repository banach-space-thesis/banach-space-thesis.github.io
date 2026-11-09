import ThesisCommon.Analysis.LpHaarNormalizedTraces
import ThesisCommon.Analysis.LpHaarSequentialGeometry

/-! Recursive trace balancing with strictly increasing underlying Haar
levels. The limiting trace and the actual multiplier diagonal are both
controlled at every node by a prescribed positive error budget. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lpHaar_infinite_trace_selection
    (d : ∀ n, Fin (2 ^ n) → 𝕜) {M : ℝ} (hM : 0 ≤ M) (hd : ∀ n k, ‖d n k‖ ≤ M)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) :
    ∃ a : LpHaarDyadicSetIndex → 𝕜, ∃ F : LpHaarSequentialSplits,
      (∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → a i = a j) ∧
      (∀ i j, i < j → (F.node i).level < (F.node j).level) ∧
      (∀ j, ‖lpHaarSplitDiagonal d (F.node j) - lpHaarParentTrace a (F.node j).parent‖ < ε j) ∧
      ∀ j (b : Bool),
        ‖lpHaarParentTrace a ((F.node j).child b) - lpHaarParentTrace a (F.node j).parent‖ < ε j := by
  obtain ⟨a, r, hr, ha, hlim, heq, hadd⟩ := lpHaar_trace_limit_finitely_additive d hM hd
  let R (j : ℕ) (P : LpHaarFiniteParent) (h : Fin j → LpHaarFiniteSplit)
      (S : LpHaarFiniteSplit) : Prop :=
    (∀ i : Fin j, (h i).level < S.level) ∧
    ‖lpHaarSplitDiagonal d S - lpHaarParentTrace a P‖ < ε j ∧
    ∀ b : Bool, ‖lpHaarParentTrace a (S.child b) - lpHaarParentTrace a P‖ < ε j
  obtain ⟨F, hF⟩ := exists_haar_split_history R (fun j P h => by
    let N := max j ((∑ i : Fin j, (h i).level) + 1)
    obtain ⟨S, hN, hP, hs, hc⟩ :=
      lpHaar_trace_parent_select_normalized d a r hr hM ha hlim heq hadd P N (hε j)
    refine ⟨S, (le_max_left _ _).trans hN, hP, ?_, hs, hc⟩
    intro i
    have hi : (h i).level ≤ ∑ k : Fin j, (h k).level :=
      Finset.single_le_sum (f := fun k : Fin j => (h k).level)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have ht := (le_max_right j ((∑ k : Fin j, (h k).level) + 1)).trans hN
    omega)
  have hp (j : ℕ) : lpHaarParentTrace a
      (lpHaarHistoryParent j (fun i : Fin j => F.node i.val)) = lpHaarParentTrace a (F.node j).parent :=
    lpHaarParentTrace_congr a heq _ _ (F.parent j).symm
  refine ⟨a, F, heq, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hF j).1 ⟨i, hij⟩
  · intro j
    simpa only [R, hp j] using (hF j).2.1
  · intro j b
    simpa only [R, hp j] using (hF j).2.2 b

end ThesisCommon
