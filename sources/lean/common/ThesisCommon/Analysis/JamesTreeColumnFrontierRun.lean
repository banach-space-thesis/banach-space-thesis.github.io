import ThesisCommon.Analysis.JamesTreeColumnFrontierStep
import ThesisCommon.Analysis.DyadicEmbeddingStabilization

/-! Iterating the actual finite-column pruning step and taking its genuine
stabilized strong subtree.  Each frontier root continues along one fixed
path until it is selected. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

structure JamesTreeColumnFrontierRun
    (d : DyadicDelayedFork)
    (Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (ε : ℕ → ℝ)
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B) where
  state : ∀ n, JamesTreeColumnFrontierState d Q ε hB n
  processed : ∀ n s, dyadicTreeEnumeration.symm s < n →
    (state (n+1)).tree s=(state n).tree s
  advance : ∀ n s, s∈dyadicTreeFrontier n →
    ((state n).tree s).IsPrefix ((state (n+1)).tree s)
  head : ∀ n,
    ‖jamesTreeMask (dyadicInitialLevels (state n).cutoff) (hL _)
      (Q (jamesTreeUnit (d.node ((state (n+1)).tree (dyadicTreeEnumeration n)))))‖ < ε n

theorem exists_jamesTreeColumnFrontierRun
    (d : DyadicDelayedFork)
    (Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (hS : JamesTreeSegmentsAreChains S)
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hLt : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)ᶜ)
    (hC : ∀ r, JamesTreeMaskClosed S (dyadicDescendantCone r))
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B)
    (hp : 1 < p.val.toReal)
    (hfinite : ∀ v, jamesTreeMask (dyadicInitialLevels (d.fork v).length) (hL _)
      (Q (jamesTreeUnit (d.node v))) = Q (jamesTreeUnit (d.node v)))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (e₀ : DyadicSubtreeEmbedding) :
    Nonempty (JamesTreeColumnFrontierRun d Q ε hL hB) := by
  classical
  let hn := fun {n : ℕ} (a : JamesTreeColumnFrontierState d Q ε hB n) =>
    JamesTreeColumnFrontierState.exists_next d Q hS hL hLt hC hB hp hfinite ε hε a
  let next : ∀ n, JamesTreeColumnFrontierState d Q ε hB n →
      JamesTreeColumnFrontierState d Q ε hB (n+1) := fun _ a => (hn a).choose
  let a : ∀ n, JamesTreeColumnFrontierState d Q ε hB n :=
    fun n => Nat.rec (JamesTreeColumnFrontierState.initial e₀) next n
  refine ⟨⟨a,?_,?_,?_⟩⟩
  · intro n s hs
    exact (hn (a n)).choose_spec.1 s hs
  · intro n s hs
    exact (hn (a n)).choose_spec.2.1 s hs
  · intro n
    exact (hn (a n)).choose_spec.2.2

namespace JamesTreeColumnFrontierRun
variable {d : DyadicDelayedFork}
  {Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S}
  {ε : ℕ → ℝ}
  {hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)}
  {hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B}

def tree (a : JamesTreeColumnFrontierRun d Q ε hL hB) : DyadicSubtreeEmbedding :=
  dyadicStabilizedEmbedding (fun n => (a.state n).tree) a.processed

theorem tree_eq_stage (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    {n : ℕ} {s : DyadicTreeNode} (hs : dyadicTreeEnumeration.symm s<n) :
    a.tree s=(a.state n).tree s :=
  dyadicStabilizedEmbedding_eq_stage (fun n => (a.state n).tree) a.processed hs

theorem tree_current (a : JamesTreeColumnFrontierRun d Q ε hL hB) (n : ℕ) :
    a.tree (dyadicTreeEnumeration n)=(a.state (n+1)).tree (dyadicTreeEnumeration n) :=
  a.tree_eq_stage (by simp only [Equiv.symm_apply_apply]; omega)

theorem frontier_prefix_stage (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    {n : ℕ} {s : DyadicTreeNode} (hs : s∈dyadicTreeFrontier n)
    {m : ℕ} (hnm : n≤m) (hm : m≤dyadicTreeEnumeration.symm s+1) :
    ((a.state n).tree s).IsPrefix ((a.state m).tree s) := by
  induction m,hnm using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m hnm ih =>
    have hm0 : m≤dyadicTreeEnumeration.symm s := by omega
    have hs0 := (mem_dyadicTreeFrontier n s).mp hs
    have hsm : s∈dyadicTreeFrontier m := (mem_dyadicTreeFrontier m s).mpr
      ⟨hm0,fun t ht hne => (hs0.2 t ht hne).trans_le hnm⟩
    exact (ih (by omega)).trans (a.advance m s hsm)

theorem frontier_prefix (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    {n : ℕ} {s : DyadicTreeNode} (hs : s∈dyadicTreeFrontier n) :
    ((a.state n).tree s).IsPrefix (a.tree s) := by
  rw [a.tree_eq_stage (n := dyadicTreeEnumeration.symm s+1) (by omega)]
  exact a.frontier_prefix_stage hs
    (((mem_dyadicTreeFrontier n s).mp hs).1.trans (Nat.le_succ _)) le_rfl

theorem frontier_anchor (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    {n : ℕ} {s : DyadicTreeNode} (hs : s∈dyadicTreeFrontier n) :
    dyadicCellAnchor (d.fork.comp a.tree) s =
      dyadicCellAnchor (d.fork.comp (a.state n).tree) s :=
  dyadicCellAnchor_eq_of_frontier_agreement d n (a.state n).tree a.tree
    (fun _ ht => a.tree_eq_stage ht) hs

theorem head_small (a : JamesTreeColumnFrontierRun d Q ε hL hB) (n : ℕ) :
    ‖jamesTreeMask (dyadicInitialLevels (a.state n).cutoff) (hL _)
      (Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration n)))))‖ < ε n := by
  rw [a.tree_current n]
  exact a.head n

theorem frontier_separation (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    {i n : ℕ} (hi : i<n) {s : DyadicTreeNode} (hs : s∈dyadicTreeFrontier n) :
    (d.fork (a.tree (dyadicTreeEnumeration i))).length < (d.node (a.tree s)).length := by
  rw [a.tree_eq_stage (n := n) (by simpa only [Equiv.symm_apply_apply] using hi)]
  exact ((a.state n).separation i hi s hs).trans_le
    ((d.node_prefix_iff _ _).mpr (a.frontier_prefix hs)).length_le

end JamesTreeColumnFrontierRun
end ThesisCommon
