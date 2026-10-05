import ThesisCommon.Analysis.JamesTreeDisjointMasks
import ThesisCommon.Analysis.JamesTreeSchauderBasis
import ThesisCommon.Analysis.JamesTreeConcreteBranches
import ThesisCommon.Analysis.JamesTreePrefixSegments

/-! Actual branch, cone, and tail coordinate masks for both segment
conventions, with a finite disjoint-tail estimate and its small-mask
consequence. These are geometric properties of the given tree norms. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

def dyadicDescendantCone (u : DyadicTreeNode) : Set DyadicTreeNode := {t | u.IsPrefix t}

theorem literalJamesTreeMaskClosed_cone (u : DyadicTreeNode) :
    JamesTreeMaskClosed literalTreeSegmentFamily (dyadicDescendantCone u) :=
  literalJamesTreeMaskClosed_set _

theorem consecutiveJamesTreeMaskClosed_orderConvex
    (B : Set DyadicTreeNode)
    (hB : ∀ s ∈ B, ∀ t ∈ B, ∀ u, s.IsPrefix u → u.IsPrefix t → u ∈ B) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily B := by
  intro A hA hne
  refine ⟨⟨hne,?_⟩,?_⟩
  · intro s hs t ht
    exact hA.1.2 s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1
  · intro s hs t ht u hsu hut
    obtain ⟨hsA,hsB⟩ := Finset.mem_filter.mp hs
    obtain ⟨htA,htB⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨hA.2 s hsA t htA u hsu hut,hB s hsB t htB u hsu hut⟩

theorem consecutiveJamesTreeMaskClosed_cone (u : DyadicTreeNode) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily (dyadicDescendantCone u) :=
  consecutiveJamesTreeMaskClosed_orderConvex _ (fun _ hs _ _ _ hsu _ => hs.trans hsu)

theorem consecutiveJamesTreeMaskClosed_convexChain
    {B : Set DyadicTreeNode} (hB : IsConvexTreeChain B) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily B :=
  consecutiveJamesTreeMaskClosed_orderConvex B hB.2

theorem jamesTreeMaskClosed_inter {S : JamesTreeSegmentFamily}
    {A B : Set DyadicTreeNode} (hA : JamesTreeMaskClosed S A) (hB : JamesTreeMaskClosed S B) :
    JamesTreeMaskClosed S (A ∩ B) := by
  classical
  generalize heC : A ∩ B = C
  intro F hF hne
  have he : (F.filter (· ∈ A)).filter (· ∈ B) = F.filter (· ∈ C) := by
    ext t
    simp only [Finset.mem_filter, ← heC, Set.mem_inter_iff,and_assoc]
  have hnA : (F.filter (· ∈ A)).Nonempty := by
    obtain ⟨t,ht⟩ := hne
    have htC := (Finset.mem_filter.mp ht).2
    rw [← heC] at htC
    exact ⟨t,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,htC.1⟩⟩
  rw [← he]
  exact hB _ (hA _ hF hnA) (he.symm ▸ hne)

theorem consecutiveJamesTreeMaskClosed_levelTail (N : ℕ) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily (dyadicInitialLevels N)ᶜ := by
  apply consecutiveJamesTreeMaskClosed_orderConvex
  intro s hs _ _ u hsu _ hu
  exact hs (hsu.length_le.trans hu)

theorem dyadicDescendantCone_disjoint {u v : DyadicTreeNode}
    (huv : ¬u.IsPrefix v) (hvu : ¬v.IsPrefix u) :
    Disjoint (dyadicDescendantCone u) (dyadicDescendantCone v) := by
  apply Set.disjoint_left.mpr
  intro t hut hvt
  exact (List.prefix_or_prefix_of_prefix hut hvt).elim huv hvu

variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTreeMask_comp_subset
    (A B : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A) (hB : JamesTreeMaskClosed S B)
    (hAB : A ⊆ B) :
    (jamesTreeMask (𝕜 := 𝕜) (p := p) A hA).comp (jamesTreeMask B hB) = jamesTreeMask A hA := by
  apply ContinuousLinearMap.ext
  intro x
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq ((jamesTreeMask A hA).continuous.comp (jamesTreeMask B hB).continuous)
      (jamesTreeMask A hA).continuous
  · intro a
    change jamesTreeMask A hA (jamesTreeMask B hB (jamesTreeDenseEmbedding 𝕜 p S a)) = _
    simp only [jamesTreeMask_dense]
    apply congrArg (jamesTreeDenseEmbedding 𝕜 p S)
    ext t
    by_cases ht : t ∈ A
    · simp only [JamesTreePreSpace.mask_apply,if_pos ht,if_pos (hAB ht)]
    · simp only [JamesTreePreSpace.mask_apply,if_neg ht]

theorem jamesTreeMask_norm_le_of_subset
    (A B : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A) (hB : JamesTreeMaskClosed S B)
    (hAB : A ⊆ B) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreeMask A hA x‖ ≤ ‖jamesTreeMask B hB x‖ := by
  have he := DFunLike.congr_fun (jamesTreeMask_comp_subset (𝕜 := 𝕜) (p := p) A B hA hB hAB) x
  rw [← he]
  exact jamesTreeMask_norm_le A hA _

theorem exists_jamesTree_small_disjoint_mask (hp : 0 < p.val.toReal)
    {n : ℕ} (A : Fin n → Set DyadicTreeNode) (hA : ∀ i, JamesTreeMaskClosed S (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (x : SegmentJamesTreeSpace 𝕜 p S) {ε : ℝ} (hε : 0 < ε)
    (hn : ‖x‖ ^ p.val.toReal < n * ε ^ p.val.toReal) :
    ∃ i, ‖jamesTreeMask (A i) (hA i) x‖ < ε := by
  by_contra h
  push_neg at h
  have hh := jamesTree_disjoint_masks_sum_rpow_le hp A hA hd x
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Real.rpow_le_rpow hε.le (h i) hp.le)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  exact (not_lt_of_ge (hsum.trans hh)) hn

end ThesisCommon
