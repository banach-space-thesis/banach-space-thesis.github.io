import ThesisCommon.Analysis.DyadicCellAnchors
import ThesisCommon.Analysis.JamesTreeFiniteSupportPruning

/-! An analytic finite-frontier state.  The two invariants record actual
support separation and actual norms of connecting paths on every earlier
column; neither asserts the eventual operator factorization. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

structure JamesTreeColumnFrontierState
    (d : DyadicDelayedFork)
    (Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (ε : ℕ → ℝ)
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B) (n : ℕ) where
  tree : DyadicSubtreeEmbedding
  separation : ∀ i, i<n → ∀ s∈dyadicTreeFrontier n,
    (d.fork (tree (dyadicTreeEnumeration i))).length < (d.node (tree s)).length
  paths : ∀ i, i<n → ∀ s∈dyadicTreeFrontier n,
    ‖jamesTreeMask
      (dyadicTreeInterval (dyadicCellAnchor (d.fork.comp tree) s) (d.node (tree s)) :
        Set DyadicTreeNode)
      (hB _ (dyadicTreeInterval_isConvex _ _))
      (Q (jamesTreeUnit (d.node (tree (dyadicTreeEnumeration i)))))‖ ≤ 2 * ε i

namespace JamesTreeColumnFrontierState
variable {d : DyadicDelayedFork}
  {Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S}
  {ε : ℕ → ℝ}
  {hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B} {n : ℕ}

def cutoff (a : JamesTreeColumnFrontierState d Q ε hB n) : ℕ :=
  max ((dyadicTreeFrontier n).sup (fun s => (d.node (a.tree s)).length))
    ((Finset.range n).sup (fun i => (d.fork (a.tree (dyadicTreeEnumeration i))).length))

theorem node_length_le_cutoff (a : JamesTreeColumnFrontierState d Q ε hB n)
    {s : DyadicTreeNode} (hs : s∈dyadicTreeFrontier n) :
    (d.node (a.tree s)).length ≤ a.cutoff :=
  (Finset.le_sup (f := fun s => (d.node (a.tree s)).length) hs).trans (le_max_left _ _)

theorem fork_length_le_cutoff (a : JamesTreeColumnFrontierState d Q ε hB n)
    {i : ℕ} (hi : i<n) :
    (d.fork (a.tree (dyadicTreeEnumeration i))).length ≤ a.cutoff :=
  (Finset.le_sup (f := fun i => (d.fork (a.tree (dyadicTreeEnumeration i))).length)
    (Finset.mem_range.mpr hi)).trans (le_max_right _ _)

def initial (e : DyadicSubtreeEmbedding) : JamesTreeColumnFrontierState d Q ε hB 0 where
  tree := e
  separation := by intro i hi; omega
  paths := by intro i hi; omega

end JamesTreeColumnFrontierState
end ThesisCommon
