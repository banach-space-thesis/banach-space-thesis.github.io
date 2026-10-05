import ThesisCommon.Analysis.JamesTreeEnumeration
import ThesisCommon.Analysis.JamesTreeFiniteMasks
import ThesisCommon.Analysis.SchauderBasis

/-! The actual normalized, monotone Schauder bases of both completed tree
spaces, using a breadth-first enumeration. No operator factorization is
assumed or asserted. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

theorem literalJamesTreeMaskClosed_set (A : Set DyadicTreeNode) :
    JamesTreeMaskClosed literalTreeSegmentFamily A := by
  intro B hB hne
  refine ⟨hne, ?_⟩
  intro s hs t ht
  exact hB.2 s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1

theorem consecutiveJamesTreeMaskClosed_prefix_set (A : Set DyadicTreeNode)
    (hA : ∀ ⦃s t : DyadicTreeNode⦄, t ∈ A → s.IsPrefix t → s ∈ A) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily A := by
  intro B hB hne
  refine ⟨literalJamesTreeMaskClosed_set A B hB.1 hne, ?_⟩
  intro s hs t ht v hsv hvt
  obtain ⟨hsB, _⟩ := Finset.mem_filter.mp hs
  obtain ⟨htB, htA⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hB.2 s hsB t htB v hsv hvt, hA htA hvt⟩

theorem literalJamesTreeMaskClosed_initial (N : ℕ) :
    JamesTreeMaskClosed literalTreeSegmentFamily (dyadicEnumerationInitial N : Set DyadicTreeNode) :=
  literalJamesTreeMaskClosed_set _

theorem consecutiveJamesTreeMaskClosed_initial (N : ℕ) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily (dyadicEnumerationInitial N : Set DyadicTreeNode) :=
  consecutiveJamesTreeMaskClosed_prefix_set _ (fun {_ _} ht hst =>
    dyadicEnumerationInitial_prefix_closed ht hst)

variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeInitialProjection (N : ℕ)
    (hN : JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode)) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  jamesTreeMask (dyadicEnumerationInitial N : Set DyadicTreeNode) hN

theorem jamesTreeInitialProjection_apply (N : ℕ)
    (hN : JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeInitialProjection N hN x = ∑ n ∈ Finset.range N,
      jamesTreeCoordinate (dyadicTreeEnumeration n) x • jamesTreeUnit (dyadicTreeEnumeration n) := by
  rw [jamesTreeInitialProjection, jamesTreeMask_finite_sum]
  simp only [dyadicEnumerationInitial, Finset.sum_map, Equiv.toEmbedding_apply]

theorem norm_jamesTreeInitialProjection_le (N : ℕ)
    (hN : JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode)) :
    ‖jamesTreeInitialProjection (𝕜 := 𝕜) (p := p) N hN‖ ≤ 1 :=
  norm_jamesTreeMask_le _ _

theorem norm_jamesTreeInitialProjection_eq_one (N : ℕ)
    (hN : JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode)) (hpos : 0 < N) :
    ‖jamesTreeInitialProjection (𝕜 := 𝕜) (p := p) N hN‖ = 1 := by
  apply norm_jamesTreeMask_eq_one
  exact ⟨dyadicTreeEnumeration 0, by simpa using hpos⟩

theorem jamesTreeInitialProjection_tendsto
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    Tendsto (fun N => jamesTreeInitialProjection N (hS N) x) atTop (𝓝 x) := by
  apply jamesTreeMask_tendsto
  intro t
  simpa only [Finset.mem_coe, mem_dyadicEnumerationInitial] using
    (eventually_gt_atTop (dyadicTreeEnumeration.symm t))

def jamesTreeSchauderBasis
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode)) :
    NormalizedSchauderBasis 𝕜 (SegmentJamesTreeSpace 𝕜 p S) where
  vector n := jamesTreeUnit (dyadicTreeEnumeration n)
  coord n := jamesTreeCoordinate (dyadicTreeEnumeration n)
  biorthogonal i j := by simp only [jamesTreeCoordinate_unit, Equiv.apply_eq_iff_eq]
  norm_vector n := norm_jamesTreeUnit _
  expansion x := by
    simpa only [jamesTreeInitialProjection_apply] using jamesTreeInitialProjection_tendsto hS x

def literalJamesTreeSchauderBasis (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    NormalizedSchauderBasis 𝕜 (LiteralChainJamesTreeSpace 𝕜 p) :=
  jamesTreeSchauderBasis literalJamesTreeMaskClosed_initial

def consecutiveJamesTreeSchauderBasis (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    NormalizedSchauderBasis 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p) :=
  jamesTreeSchauderBasis consecutiveJamesTreeMaskClosed_initial

theorem jamesTreeSchauderBasis_partialSum_norm_le
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode))
    (N : ℕ) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖∑ n ∈ Finset.range N, (jamesTreeSchauderBasis (𝕜 := 𝕜) (p := p) hS).coord n x •
      (jamesTreeSchauderBasis (𝕜 := 𝕜) (p := p) hS).vector n‖ ≤ ‖x‖ := by
  change ‖∑ n ∈ Finset.range N, jamesTreeCoordinate (dyadicTreeEnumeration n) x •
      jamesTreeUnit (dyadicTreeEnumeration n)‖ ≤ ‖x‖
  rw [← jamesTreeInitialProjection_apply N (hS N)]
  exact jamesTreeMask_norm_le _ _ x

end ThesisCommon
