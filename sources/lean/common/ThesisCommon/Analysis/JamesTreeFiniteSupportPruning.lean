import ThesisCommon.Analysis.JamesTreeFiniteSupportGeometry

/-! The pruning step for genuinely finite columns.  Its cut is selected
after the column, so it contains the prescribed support of that column. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}
  {ι : Type*} [Fintype ι]

theorem exists_jamesTree_finite_pruned_column
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) ↔ s.IsPrefix t)
    (hS : JamesTreeSegmentsAreChains S)
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hLt : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)ᶜ)
    (hC : ∀ r, JamesTreeMaskClosed S (dyadicDescendantCone r))
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B)
    (hp : 1 < p.val.toReal)
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (L : DyadicTreeNode → ℕ)
    (hfinite : ∀ v, jamesTreeMask (dyadicInitialLevels (L v)) (hL _)
      (T (jamesTreeUnit (f v))) = T (jamesTreeUnit (f v)))
    (u₀ : DyadicTreeNode) (u : ι → DyadicTreeNode) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : DyadicTreeNode) (M : ℕ) (w t : ι → DyadicTreeNode),
      u₀.IsPrefix v ∧ v ≠ u₀ ∧ N < M ∧ L v ≤ M ∧
      ‖jamesTreeMask (dyadicInitialLevels N) (hL N) (T (jamesTreeUnit (f v)))‖ < ε ∧
      jamesTreeMask (dyadicInitialLevels M) (hL M) (T (jamesTreeUnit (f v))) =
        T (jamesTreeUnit (f v)) ∧
      ∀ i, (u i).IsPrefix (w i) ∧ (f (u i)).IsPrefix (t i) ∧
        (t i).IsPrefix (f (w i)) ∧ (t i).length = M + 1 ∧ M + 1 < (f (w i)).length ∧
        ‖jamesTreeMask (dyadicTreeInterval (f (u i)) (t i) : Set DyadicTreeNode)
          (hB _ (dyadicTreeInterval_isConvex _ _)) (T (jamesTreeUnit (f v)))‖ < ε := by
  obtain ⟨v,M,w,t,hv,hne,hNM,hLM,hhead,_,hpaths⟩ :=
    exists_jamesTree_pruned_column_above f hf hS hL hLt hC hB hp T u₀ u N L hε
  exact ⟨v,M,w,t,(hf _ _).mp hv,fun h => hne (congrArg f h),hNM,hLM,hhead,
    jamesTreeMask_fix_of_level_support hL _ (hfinite v) hLM,hpaths⟩

theorem jamesTreeIntervalMask_norm_le_head_add_path
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hLt : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)ᶜ)
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B)
    (x : SegmentJamesTreeSpace 𝕜 p S) (a r t : DyadicTreeNode)
    (hrt : r.IsPrefix t) {N : ℕ} (hrN : r.length ≤ N) :
    ‖jamesTreeMask (dyadicTreeInterval a t : Set DyadicTreeNode)
      (hB _ (dyadicTreeInterval_isConvex _ _)) x‖ ≤
    ‖jamesTreeMask (dyadicInitialLevels N) (hL N) x‖ +
    ‖jamesTreeMask (dyadicTreeInterval r t : Set DyadicTreeNode)
      (hB _ (dyadicTreeInterval_isConvex _ _)) x‖ := by
  apply jamesTreeMask_norm_le_of_cover hL _ _ _
    (hB _ (dyadicTreeInterval_isConvex _ _)) (hL N)
    (hB _ (dyadicTreeInterval_isConvex _ _)) (hLt N) _ x
  intro z hz
  have hzt := ((mem_dyadicTreeInterval a t z).mp hz).2
  rcases List.prefix_or_prefix_of_prefix hzt hrt with hzr | hrz
  · exact Or.inl (hzr.length_le.trans hrN)
  · exact Or.inr ((mem_dyadicTreeInterval r t z).mpr ⟨hrz,hzt⟩)

end ThesisCommon
