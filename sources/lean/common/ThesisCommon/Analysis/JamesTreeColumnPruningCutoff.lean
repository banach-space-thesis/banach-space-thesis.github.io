import ThesisCommon.Analysis.JamesTreeMaskSplitting
import ThesisCommon.Analysis.DyadicConePruningGeometry
import ThesisCommon.Analysis.JamesTreeSmallLevelImages

/-! Andrew's finite column-pruning step with a prescribed node-dependent lower bound on the terminal cut on the actual completed tree
spaces. Many incomparable descendant cones supply the small branch, while
the finite-level weak-null theorem supplies the small common head. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}
  {ι : Type*} [Fintype ι]

theorem exists_jamesTree_pruned_column_above
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) ↔ s.IsPrefix t)
    (hS : JamesTreeSegmentsAreChains S)
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hLt : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)ᶜ)
    (hC : ∀ r, JamesTreeMaskClosed S (dyadicDescendantCone r))
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B)
    (hp : 1 < p.val.toReal)
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (u₀ : DyadicTreeNode) (u : ι → DyadicTreeNode) (N : ℕ) (L : DyadicTreeNode → ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : DyadicTreeNode) (M : ℕ) (w t : ι → DyadicTreeNode),
      (f u₀).IsPrefix (f v) ∧ f v ≠ f u₀ ∧ N < M ∧ L v ≤ M ∧
      ‖jamesTreeMask (dyadicInitialLevels N) (hL N) (T (jamesTreeUnit (f v)))‖ < ε ∧
      ‖T (jamesTreeUnit (f v)) -
        jamesTreeMask (dyadicInitialLevels M) (hL M) (T (jamesTreeUnit (f v)))‖ < ε ∧
      ∀ i, (u i).IsPrefix (w i) ∧ (f (u i)).IsPrefix (t i) ∧
        (t i).IsPrefix (f (w i)) ∧ (t i).length = M + 1 ∧ M + 1 < (f (w i)).length ∧
        ‖jamesTreeMask (dyadicTreeInterval (f (u i)) (t i) : Set DyadicTreeNode)
          (hB _ (dyadicTreeInterval_isConvex _ _)) (T (jamesTreeUnit (f v)))‖ < ε := by
  classical
  have hp0 : 0 < p.val.toReal := lt_trans zero_lt_one hp
  have he2 : 0 < ε / 2 := half_pos hε
  have hep : 0 < (ε / 2) ^ p.val.toReal := Real.rpow_pos_of_pos he2 _
  obtain ⟨n, hn⟩ := exists_nat_gt (‖T‖ ^ p.val.toReal / (ε / 2) ^ p.val.toReal)
  have hn' : ‖T‖ ^ p.val.toReal < n * (ε / 2) ^ p.val.toReal :=
    (div_lt_iff₀ hep).mp hn
  let r : ι → Fin n → DyadicTreeNode := fun i j => dyadicCombEmbedding (u i) j.val
  let N₁ := max (N + 1) (Finset.univ.sup (fun q : ι × Fin n => (f (r q.1 q.2)).length))
  have hNN : N < N₁ := Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_left _ _)
  have hrN : ∀ i j, (f (r i j)).length ≤ N₁ := fun i j =>
    (Finset.le_sup (f := fun q : ι × Fin n => (f (r q.1 q.2)).length)
      (Finset.mem_univ (i,j))).trans (le_max_right _ _)
  obtain ⟨v, hv, hvne, hvsmall⟩ :=
    exists_jamesTree_subtree_small_level_image f hf hS hp T u₀ N₁ (hL N₁) he2
  let x := T (jamesTreeUnit (f v))
  have hx : ‖x‖ ≤ ‖T‖ := by
    simpa only [x, norm_jamesTreeUnit, mul_one] using T.le_opNorm (jamesTreeUnit (f v))
  have hchoice : ∀ i, ∃ j : Fin n,
      ‖jamesTreeMask (dyadicDescendantCone (f (r i j))) (hC _) x‖ < ε / 2 := by
    intro i
    refine exists_jamesTree_small_disjoint_mask hp0
      (fun j => dyadicDescendantCone (f (r i j))) (fun j => hC _) ?_ x he2 ?_
    · intro j k hjk
      apply dyadicDescendantCone_disjoint
      · intro h
        exact dyadicCombEmbedding_antichain (u i) j.val k.val
          (fun h => hjk (Fin.ext h)) ((hf _ _).mp h)
      · intro h
        exact dyadicCombEmbedding_antichain (u i) k.val j.val
          (fun h => hjk (Fin.ext h.symm)) ((hf _ _).mp h)
    · exact (Real.rpow_le_rpow (norm_nonneg _) hx hp0.le).trans_lt hn'
  choose j hj using hchoice
  have htail : ∀ᶠ M : ℕ in atTop,
      ‖x - jamesTreeMask (dyadicInitialLevels M) (hL M) x‖ < ε :=
    (tendsto_order.mp (jamesTreeLevelTail_tendsto hL x).norm).2 ε
      (by simpa only [norm_zero] using hε)
  obtain ⟨M,hNM0,hM⟩ := ((eventually_ge_atTop (max N₁ (L v))).and htail).exists
  have hNM : N₁ ≤ M := (le_max_left _ _).trans hNM0
  have hLM : L v ≤ M := (le_max_right _ _).trans hNM0
  have hext : ∀ i, ∃ w t, (r i (j i)).IsPrefix w ∧ (f (u i)).IsPrefix t ∧
      (f (r i (j i))).IsPrefix t ∧ t.IsPrefix (f w) ∧ t.length = M + 1 ∧
      M + 1 < (f w).length ∧
      (dyadicTreeInterval (f (u i)) t : Set DyadicTreeNode) ⊆
        dyadicInitialLevels N₁ ∪ dyadicDescendantCone (f (r i (j i))) :=
    fun i => exists_dyadic_interval_through_cone f hf
      (dyadicCombEmbedding_prefix (u i) (j i).val) (hrN i (j i)) hNM
  choose w t hrw hut hrt htw htl hwl hcover using hext
  refine ⟨v,M,w,t,hv,hvne,hNN.trans_le hNM,hLM,?_,hM,?_⟩
  · exact (jamesTreeMask_norm_le_of_subset (dyadicInitialLevels N) (dyadicInitialLevels N₁)
      (hL N) (hL N₁) (fun _ h => h.trans hNN.le) x).trans_lt
      (hvsmall.trans (by linarith))
  · intro i
    refine ⟨(dyadicCombEmbedding_prefix (u i) (j i).val).trans (hrw i),
      hut i,htw i,htl i,hwl i,?_⟩
    have hh := jamesTreeMask_norm_le_of_cover hL
      (dyadicTreeInterval (f (u i)) (t i) : Set DyadicTreeNode)
      (dyadicInitialLevels N₁) (dyadicDescendantCone (f (r i (j i))))
      (hB _ (dyadicTreeInterval_isConvex _ _)) (hL N₁) (hC _) (hLt N₁) (hcover i) x
    exact hh.trans_lt (by have := add_lt_add hvsmall (hj i); linarith)

end ThesisCommon
