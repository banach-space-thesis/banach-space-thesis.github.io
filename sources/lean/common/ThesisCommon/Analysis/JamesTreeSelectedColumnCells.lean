import ThesisCommon.Analysis.JamesTreeColumnFrontierRun

/-! Bounds on the actual final connecting cells of the recursively
selected tree.  Only the finite frontier can meet an old column; deeper
cells are proved to vanish from their actual support geometry. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

namespace JamesTreeColumnFrontierRun
variable {d : DyadicDelayedFork}
  {Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S}
  {ε : ℕ → ℝ}
  {hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)}
  {hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B}

theorem frontier_cell_small (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    (hfinite : ∀ v, jamesTreeMask (dyadicInitialLevels (d.fork v).length) (hL _)
      (Q (jamesTreeUnit (d.node v))) = Q (jamesTreeUnit (d.node v)))
    {i n : ℕ} (hi : i<n) {s : DyadicTreeNode} (hs : s∈dyadicTreeFrontier n) :
    ‖jamesTreeMask
      (dyadicTreeInterval (dyadicCellAnchor (d.fork.comp a.tree) s) (d.fork (a.tree s)) :
        Set DyadicTreeNode) (hB _ (dyadicTreeInterval_isConvex _ _))
      (Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration i)))))‖ ≤ 2*ε i := by
  rw [a.frontier_anchor hs,
    a.tree_eq_stage (n := n) (s := dyadicTreeEnumeration i)
      (by simpa only [Equiv.symm_apply_apply] using hi)]
  have hpref : (d.node ((a.state n).tree s)).IsPrefix (d.fork (a.tree s)) :=
    ((d.node_prefix_iff _ _).mpr (a.frontier_prefix hs)).trans
      (dyadicRootedCell_prefix_endpoint d.fork (d.node_mem (a.tree s)))
  rw [jamesTreeIntervalMask_extend_of_support hL hB _
    (hfinite ((a.state n).tree (dyadicTreeEnumeration i))) _
    (d.node ((a.state n).tree s)) _ hpref ((a.state n).separation i hi s hs).le]
  exact (a.state n).paths i hi s hs

theorem processed_fork_le_cutoff (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    {i : ℕ} {s : DyadicTreeNode} (hs : dyadicTreeEnumeration.symm s < i) :
    (d.fork (a.tree s)).length ≤ (a.state i).cutoff := by
  rw [a.tree_eq_stage hs]
  simpa only [Equiv.apply_symm_apply] using (a.state i).fork_length_le_cutoff hs

theorem earlier_cell_small (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    {i : ℕ} {s : DyadicTreeNode} (hs : dyadicTreeEnumeration.symm s < i) :
    ‖jamesTreeMask
      (dyadicTreeInterval (dyadicCellAnchor (d.fork.comp a.tree) s) (d.fork (a.tree s)) :
        Set DyadicTreeNode) (hB _ (dyadicTreeInterval_isConvex _ _))
      (Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration i)))))‖ < ε i := by
  refine (jamesTreeMask_norm_le_of_subset _ (dyadicInitialLevels (a.state i).cutoff)
    (hB _ (dyadicTreeInterval_isConvex _ _)) (hL _) ?_ _).trans_lt (a.head_small i)
  intro t ht
  exact (((mem_dyadicTreeInterval _ _ _).mp ht).2.length_le).trans (a.processed_fork_le_cutoff hs)

theorem later_cell_zero (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    (hfinite : ∀ v, jamesTreeMask (dyadicInitialLevels (d.fork v).length) (hL _)
      (Q (jamesTreeUnit (d.node v))) = Q (jamesTreeUnit (d.node v)))
    {i n : ℕ} (hi : i<n) {s : DyadicTreeNode}
    (hs : n≤dyadicTreeEnumeration.symm s) (hsF : s∉dyadicTreeFrontier n) :
    jamesTreeMask
      (dyadicTreeInterval (dyadicCellAnchor (d.fork.comp a.tree) s) (d.fork (a.tree s)) :
        Set DyadicTreeNode) (hB _ (dyadicTreeInterval_isConvex _ _))
      (Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration i))))) = 0 := by
  obtain ⟨t,ht,hts⟩ := exists_dyadicTreeFrontier_prefix n s hs
  have hne : t≠s := by intro h; exact hsF (h ▸ ht)
  apply jamesTreeCoordinate_ext hL
  intro z
  rw [jamesTreeCoordinate_mask,map_zero]
  split_ifs with hz
  · have hzcell : z∈dyadicRootedCell (d.fork.comp a.tree) s := by
      rw [dyadicRootedCell_eq_interval]
      exact hz
    have htz := dyadicRootedCell_ancestor_prefix (d.fork.comp a.tree) hzcell hts hne
    have hlen : (d.fork (a.tree (dyadicTreeEnumeration i))).length < z.length :=
      (a.frontier_separation hi ht).trans_le
        ((dyadicRootedCell_prefix_endpoint d.fork (d.node_mem (a.tree t))).length_le.trans htz.length_le)
    exact jamesTreeCoordinate_zero_of_level_support hL _ (hfinite _) hlen
  · rfl

theorem parent_fork_le_cutoff (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    (s : DyadicTreeNode) (b : Bool) :
    (d.fork (a.tree s)).length ≤ (a.state (dyadicTreeEnumeration.symm (s++[b]))).cutoff :=
  a.processed_fork_le_cutoff (dyadicTreeEnumeration_child_index s b)

end JamesTreeColumnFrontierRun
end ThesisCommon
