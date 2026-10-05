import ThesisCommon.Analysis.JamesTreeColumnFrontierState
import ThesisCommon.Analysis.DyadicTreeFrontierGrafts

/-! An actual operator-dependent frontier update.  Finite-column pruning
chooses the new roots, and finite support proves that every earlier path
estimate survives the update. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

set_option maxHeartbeats 1200000 in
theorem JamesTreeColumnFrontierState.exists_next
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
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    {n : ℕ} (a : JamesTreeColumnFrontierState d Q ε hB n) :
    ∃ b : JamesTreeColumnFrontierState d Q ε hB (n+1),
      (∀ s, dyadicTreeEnumeration.symm s < n → b.tree s = a.tree s) ∧
      (∀ s∈dyadicTreeFrontier n, (a.tree s).IsPrefix (b.tree s)) ∧
      ‖jamesTreeMask (dyadicInitialLevels a.cutoff) (hL _)
        (Q (jamesTreeUnit (d.node (b.tree (dyadicTreeEnumeration n)))))‖ < ε n := by
  classical
  let c := dyadicTreeEnumeration n
  let I := {s // s∈(dyadicTreeFrontier n).erase c}
  obtain ⟨v,M,w,t,hv,_,hNM,hvM,hhead,hfix,hpaths⟩ :=
    exists_jamesTree_finite_pruned_column d.nodeEmbedding d.node_prefix_iff
      hS hL hLt hC hB hp Q (fun v => (d.fork v).length) hfinite
      (a.tree c) (fun i : I => a.tree i.val) a.cutoff (hε n)
  let r : DyadicTreeNode → DyadicTreeNode := fun s =>
    if s=c then v else if hs : s∈(dyadicTreeFrontier n).erase c then w ⟨s,hs⟩ else a.tree s
  have hr : ∀ s∈dyadicTreeFrontier n, (a.tree s).IsPrefix (r s) := by
    intro s hs
    by_cases hsc : s=c
    · simpa only [r,if_pos hsc,hsc] using hv
    · have hi := Finset.mem_erase.mpr ⟨hsc,hs⟩
      simpa only [r,if_neg hsc,dif_pos hi] using (hpaths ⟨s,hi⟩).1
  let e := dyadicFrontierGraft n a.tree r hr
  have he : ∀ s, dyadicTreeEnumeration.symm s < n → e s=a.tree s :=
    fun _ hs => dyadicFrontierGraft_processed n a.tree r hr hs
  have hec : e c=v := by
    rw [dyadicFrontierGraft_frontier n a.tree r hr (dyadicTreeEnumeration_mem_frontier n)]
    simp [r,c]
  have hec0 : e (dyadicTreeEnumeration n)=v := hec
  have hes : ∀ s (hs : s∈(dyadicTreeFrontier n).erase c), e s=w ⟨s,hs⟩ := by
    intro s hs
    rw [dyadicFrontierGraft_frontier n a.tree r hr (Finset.mem_erase.mp hs).2]
    simp only [r,if_neg (Finset.mem_erase.mp hs).1,dif_pos hs]
  have hep : ∀ s∈dyadicTreeFrontier n, (a.tree s).IsPrefix (e s) := by
    intro s hs
    rw [dyadicFrontierGraft_frontier n a.tree r hr hs]
    exact hr s hs
  have hei : ∀ i, i<n → e (dyadicTreeEnumeration i)=a.tree (dyadicTreeEnumeration i) :=
    fun i hi => he _ (by simpa only [Equiv.symm_apply_apply] using hi)
  have hanc : ∀ s∈dyadicTreeFrontier n,
      dyadicCellAnchor (d.fork.comp e) s=dyadicCellAnchor (d.fork.comp a.tree) s :=
    fun _ hs => dyadicCellAnchor_eq_of_frontier_agreement d n a.tree e he hs
  have hvc : ∀ i, i<n → (d.fork (a.tree (dyadicTreeEnumeration i))).length < (d.fork v).length := by
    intro i hi
    exact (a.separation i hi c (dyadicTreeEnumeration_mem_frontier n)).trans_le
      (((d.node_prefix_iff _ _).mpr hv).length_le.trans
        (dyadicRootedCell_prefix_endpoint d.fork (d.node_mem v)).length_le)
  have hsep : ∀ i, i<n+1 → ∀ s∈dyadicTreeFrontier (n+1),
      (d.fork (e (dyadicTreeEnumeration i))).length < (d.node (e s)).length := by
    intro i hi s hs
    rcases (mem_dyadicTreeFrontier_succ_iff n s).mp hs with ⟨hs,hsc⟩ | ⟨b,rfl⟩
    · have his : s∈(dyadicTreeFrontier n).erase c := Finset.mem_erase.mpr ⟨hsc,hs⟩
      rw [hes s his]
      by_cases hin : i=n
      · subst i
        rw [hec]
        exact (hvM.trans (Nat.le_succ M)).trans_lt (hpaths ⟨s,his⟩).2.2.2.2.1
      · have hi0 : i<n := by omega
        rw [hei i hi0]
        exact (a.separation i hi0 s hs).trans_le
          ((d.node_prefix_iff _ _).mpr (hpaths ⟨s,his⟩).1).length_le
    · have hchild := dyadicDelayedFork_child_node_length d e c b
      rw [hec] at hchild
      by_cases hin : i=n
      · subst i; simpa only [hec0,c] using hchild
      · have hi0 : i<n := by omega
        rw [hei i hi0]
        exact (hvc i hi0).trans hchild
  have hnorm : ∀ i, i<n+1 → ∀ s∈dyadicTreeFrontier (n+1),
      ‖jamesTreeMask
        (dyadicTreeInterval (dyadicCellAnchor (d.fork.comp e) s) (d.node (e s)) : Set DyadicTreeNode)
        (hB _ (dyadicTreeInterval_isConvex _ _))
        (Q (jamesTreeUnit (d.node (e (dyadicTreeEnumeration i)))))‖ ≤ 2*ε i := by
    intro i hi s hs
    rcases (mem_dyadicTreeFrontier_succ_iff n s).mp hs with ⟨hs,hsc⟩ | ⟨b,rfl⟩
    · have his : s∈(dyadicTreeFrontier n).erase c := Finset.mem_erase.mpr ⟨hsc,hs⟩
      rw [hanc s hs,hes s his]
      by_cases hin : i=n
      · subst i
        rw [hec]
        have hext := jamesTreeIntervalMask_extend_of_support hL hB
          (Q (jamesTreeUnit (d.node v))) hfix
          (dyadicCellAnchor (d.fork.comp a.tree) s) (t ⟨s,his⟩) (d.node (w ⟨s,his⟩))
          (hpaths ⟨s,his⟩).2.2.1 (by rw [(hpaths ⟨s,his⟩).2.2.2.1]; omega)
        rw [hext]
        have hb := jamesTreeIntervalMask_norm_le_head_add_path hL hLt hB
          (Q (jamesTreeUnit (d.node v))) (dyadicCellAnchor (d.fork.comp a.tree) s)
          (d.node (a.tree s)) (t ⟨s,his⟩) (hpaths ⟨s,his⟩).2.1
          (a.node_length_le_cutoff hs)
        have hsm := (hpaths ⟨s,his⟩).2.2.2.2.2
        exact hb.trans ((add_le_add hhead.le hsm.le).trans_eq (by ring))
      · have hi0 : i<n := by omega
        rw [hei i hi0]
        rw [jamesTreeIntervalMask_extend_of_support hL hB _
          (hfinite (a.tree (dyadicTreeEnumeration i))) _ (d.node (a.tree s)) _
          ((d.node_prefix_iff _ _).mpr (hpaths ⟨s,his⟩).1) (a.separation i hi0 s hs).le]
        exact a.paths i hi0 s hs
    · rw [dyadicCellAnchor_snoc]
      change ‖jamesTreeMask (dyadicTreeInterval (d.fork (e c)++[b])
        (d.node (e (c++[b]))) : Set DyadicTreeNode) _
        (Q (jamesTreeUnit (d.node (e (dyadicTreeEnumeration i)))))‖ ≤ 2*ε i
      have hlen : (d.fork (e (dyadicTreeEnumeration i))).length < (d.fork (e c)++[b]).length := by
        simp only [List.length_append,List.length_singleton]
        rw [hec]
        by_cases hin : i=n
        · subst i; rw [hec0]; omega
        · have hi0 : i<n := by omega
          rw [hei i hi0]
          exact (hvc i hi0).trans (Nat.lt_succ_self _)
      rw [jamesTreeIntervalMask_zero_of_support hL hB _
        (hfinite (e (dyadicTreeEnumeration i))) _ _ hlen,norm_zero]
      exact mul_nonneg (by norm_num) (hε i).le
  let b : JamesTreeColumnFrontierState d Q ε hB (n+1) := ⟨e,hsep,hnorm⟩
  refine ⟨b,he,hep,?_⟩
  change ‖jamesTreeMask (dyadicInitialLevels a.cutoff) (hL _)
    (Q (jamesTreeUnit (d.node (e c))))‖ < ε n
  rw [hec]
  exact hhead

end ThesisCommon
