import ThesisCommon.Analysis.JamesTreePrefixSegments
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-! Pulling finite segments back to an actual prefix subtree preserves both
recorded segment conventions whenever the pullback is nonempty. -/
noncomputable section
namespace ThesisCommon

def prefixPullback (u : DyadicTreeNode) (A : Finset DyadicTreeNode) :
    Finset DyadicTreeNode :=
  A.preimage (dyadicPrefixEmbedding u) (dyadicPrefixEmbedding u).injective.injOn

@[simp] theorem mem_prefixPullback (u t : DyadicTreeNode) (A : Finset DyadicTreeNode) :
    t ∈ prefixPullback u A ↔ u ++ t ∈ A := Finset.mem_preimage

theorem literalTreeSegment_prefixPullback {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) (u : DyadicTreeNode)
    (hne : (prefixPullback u A).Nonempty) :
    IsLiteralTreeSegment (prefixPullback u A) := by
  refine ⟨hne, ?_⟩
  intro s hs t ht
  have h := hA.2 (u ++ s) ((mem_prefixPullback u s A).mp hs)
    (u ++ t) ((mem_prefixPullback u t A).mp ht)
  simpa only [List.prefix_append_right_inj] using h

theorem consecutiveTreeSegment_prefixPullback {A : Finset DyadicTreeNode}
    (hA : IsConsecutiveTreeSegment A) (u : DyadicTreeNode)
    (hne : (prefixPullback u A).Nonempty) :
    IsConsecutiveTreeSegment (prefixPullback u A) := by
  refine ⟨literalTreeSegment_prefixPullback hA.1 u hne, ?_⟩
  intro s hs t ht v hsv hvt
  apply (mem_prefixPullback u v A).mpr
  exact hA.2 (u ++ s) ((mem_prefixPullback u s A).mp hs)
    (u ++ t) ((mem_prefixPullback u t A).mp ht) (u ++ v)
    ((List.prefix_append_right_inj u).mpr hsv)
    ((List.prefix_append_right_inj u).mpr hvt)

theorem prefixPullback_disjoint (u : DyadicTreeNode) {A B : Finset DyadicTreeNode}
    (h : Disjoint A B) : Disjoint (prefixPullback u A) (prefixPullback u B) := by
  apply Finset.disjoint_left.mpr
  intro t htA htB
  exact Finset.disjoint_left.mp h ((mem_prefixPullback u t A).mp htA)
    ((mem_prefixPullback u t B).mp htB)

theorem sum_mapDomain_prefix {𝕜 : Type*} [AddCommMonoid 𝕜]
    (u : DyadicTreeNode) (A : Finset DyadicTreeNode) (a : DyadicTreeNode →₀ 𝕜) :
    ∑ t ∈ A, (Finsupp.mapDomain (dyadicPrefixEmbedding u) a) t =
      ∑ t ∈ prefixPullback u A, a t := by
  classical
  have h := Finset.sum_preimage (dyadicPrefixEmbedding u) A
    (dyadicPrefixEmbedding u).injective.injOn
    (Finsupp.mapDomain (dyadicPrefixEmbedding u) a)
    (fun t _ ht => Finsupp.mapDomain_notin_range a t ht)
  simpa only [prefixPullback, Finsupp.mapDomain_apply (dyadicPrefixEmbedding u).injective]
    using h.symm

end ThesisCommon
