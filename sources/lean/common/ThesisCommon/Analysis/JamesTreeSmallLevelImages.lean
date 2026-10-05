import ThesisCommon.Analysis.JamesTreeAntichainWeakNull
import ThesisCommon.Analysis.DyadicTreeAntichains

/-! The finite-level gliding-hump step of Andrew's Proposition 2, on actual
completed tree spaces. The subtree is a genuine prefix-order embedding, not
an assumed operator-preservation interface. The proof uses its explicit
infinite antichain of descendants and the checked finite antichain norms. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem exists_jamesTree_subtree_small_level_image
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) ↔ s.IsPrefix t)
    (hS : JamesTreeSegmentsAreChains S) (hp : 1 < p.val.toReal)
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (u : DyadicTreeNode) (N : ℕ) (hN : JamesTreeMaskClosed S (dyadicInitialLevels N))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v, (f u).IsPrefix (f v) ∧ f v ≠ f u ∧
      ‖jamesTreeMask (dyadicInitialLevels N) hN (T (jamesTreeUnit (f v)))‖ < ε := by
  let e := (dyadicCombEmbedding u).trans f
  have he : IsTreeAntichainEmbedding e := treeAntichainEmbedding_comp f
    (fun s t h => (hf s t).mp h) (dyadicCombEmbedding u) (dyadicCombEmbedding_antichain u)
  have h := (jamesTree_antichain_level_image_tendsto e he hS hp T N hN).norm
  have hsmall : ∀ᶠ n : ℕ in cofinite,
      ‖jamesTreeMask (dyadicInitialLevels N) hN (T (jamesTreeUnit (e n)))‖ < ε :=
    (tendsto_order.mp h).2 ε (by simpa only [norm_zero] using hε)
  obtain ⟨n, hn⟩ := hsmall.exists
  exact ⟨dyadicCombEmbedding u n, (hf _ _).mpr (dyadicCombEmbedding_prefix u n),
    f.injective.ne (dyadicCombEmbedding_ne u n), hn⟩

theorem exists_literalJamesTree_subtree_small_level_image
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) ↔ s.IsPrefix t)
    (hp : 1 < p.val.toReal)
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p)
    (u : DyadicTreeNode) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v, (f u).IsPrefix (f v) ∧ f v ≠ f u ∧
      ‖literalJamesTreeLevelProjection p N (T (jamesTreeUnit (f v)))‖ < ε :=
  exists_jamesTree_subtree_small_level_image f hf literalJamesTreeSegmentsAreChains hp T u N
    (literalJamesTreeMaskClosed_levels N) hε

theorem exists_consecutiveJamesTree_subtree_small_level_image
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) ↔ s.IsPrefix t)
    (hp : 1 < p.val.toReal)
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p)
    (u : DyadicTreeNode) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v, (f u).IsPrefix (f v) ∧ f v ≠ f u ∧
      ‖consecutiveJamesTreeLevelProjection p N (T (jamesTreeUnit (f v)))‖ < ε :=
  exists_jamesTree_subtree_small_level_image f hf consecutiveJamesTreeSegmentsAreChains hp T u N
    (consecutiveJamesTreeMaskClosed_levels N) hε

end ThesisCommon
