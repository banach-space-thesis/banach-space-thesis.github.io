import ThesisCommon.Analysis.JamesTreeColumnPruningCutoff

/-! Exact support bookkeeping for the finite-column gliding-hump recursion.
Once a path has passed the support cut, extending that path cannot alter
its mask on the column, and every later-starting cell reads zero. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTreeCoordinate_zero_of_level_support
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    {N : ℕ} (x : SegmentJamesTreeSpace 𝕜 p S)
    (hx : jamesTreeMask (dyadicInitialLevels N) (hL N) x=x)
    {t : DyadicTreeNode} (ht : N<t.length) : jamesTreeCoordinate t x=0 := by
  have h := congrArg (jamesTreeCoordinate (𝕜 := 𝕜) (p := p) (S := S) t) hx
  rw [jamesTreeCoordinate_mask,if_neg (by exact Nat.not_le.mpr ht)] at h
  exact h.symm

theorem jamesTreeMask_fix_of_level_support
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    {N M : ℕ} (x : SegmentJamesTreeSpace 𝕜 p S)
    (hx : jamesTreeMask (dyadicInitialLevels N) (hL N) x=x) (hNM : N≤M) :
    jamesTreeMask (dyadicInitialLevels M) (hL M) x=x := by
  apply jamesTreeCoordinate_ext hL
  intro t
  rw [jamesTreeCoordinate_mask]
  split_ifs with ht
  · rfl
  · exact (jamesTreeCoordinate_zero_of_level_support hL x hx
      (lt_of_le_of_lt hNM (Nat.lt_of_not_ge ht))).symm

theorem jamesTreeIntervalMask_extend_of_support
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B)
    {N : ℕ} (x : SegmentJamesTreeSpace 𝕜 p S)
    (hx : jamesTreeMask (dyadicInitialLevels N) (hL N) x=x)
    (l r s : DyadicTreeNode) (hrs : r.IsPrefix s) (hN : N≤r.length) :
    jamesTreeMask (dyadicTreeInterval l s : Set DyadicTreeNode)
      (hB _ (dyadicTreeInterval_isConvex l s)) x =
    jamesTreeMask (dyadicTreeInterval l r : Set DyadicTreeNode)
      (hB _ (dyadicTreeInterval_isConvex l r)) x := by
  classical
  apply jamesTreeCoordinate_ext hL
  intro t
  rw [jamesTreeCoordinate_mask,jamesTreeCoordinate_mask]
  by_cases htN : N<t.length
  · simp only [jamesTreeCoordinate_zero_of_level_support hL x hx htN,ite_self]
  · have heq : t∈dyadicTreeInterval l s ↔ t∈dyadicTreeInterval l r := by
      rw [mem_dyadicTreeInterval,mem_dyadicTreeInterval]
      constructor
      · rintro ⟨hlt,hts⟩
        exact ⟨hlt,List.prefix_of_prefix_length_le hts hrs ((Nat.le_of_not_gt htN).trans hN)⟩
      · rintro ⟨hlt,htr⟩
        exact ⟨hlt,htr.trans hrs⟩
    simpa only [Finset.mem_coe,heq]

theorem jamesTreeIntervalMask_zero_of_support
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B)
    {N : ℕ} (x : SegmentJamesTreeSpace 𝕜 p S)
    (hx : jamesTreeMask (dyadicInitialLevels N) (hL N) x=x)
    (l r : DyadicTreeNode) (hl : N<l.length) :
    jamesTreeMask (dyadicTreeInterval l r : Set DyadicTreeNode)
      (hB _ (dyadicTreeInterval_isConvex l r)) x=0 := by
  classical
  apply jamesTreeCoordinate_ext hL
  intro t
  rw [jamesTreeCoordinate_mask,map_zero]
  split_ifs with ht
  · have hlt := ((mem_dyadicTreeInterval l r t).mp ht).1.length_le
    exact jamesTreeCoordinate_zero_of_level_support hL x hx (hl.trans_le hlt)
  · rfl

end ThesisCommon
