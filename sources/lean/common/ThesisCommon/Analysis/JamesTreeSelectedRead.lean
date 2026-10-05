import ThesisCommon.Analysis.DyadicSelectedCellSegments
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The actual finite-support readback over selected-subtree cells. Each
ambient coefficient is assigned to at most one cell, so this is a genuine
linear map on c00; its norm bound follows by lifting disjoint segment tests. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.JamesTreePreSpace
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def selectedReadAtom (e : DyadicSubtreeEmbedding) (t : DyadicTreeNode) : JamesTreePreSpace 𝕜 p S :=
  if h : ∃ s, t ∈ dyadicSelectedCell e s then single (Classical.choose h) 1 else 0

theorem selectedReadAtom_apply (e : DyadicSubtreeEmbedding) (t s : DyadicTreeNode) :
    selectedReadAtom (𝕜 := 𝕜) (p := p) (S := S) e t s =
      if t ∈ dyadicSelectedCell e s then 1 else 0 := by
  classical
  by_cases h : ∃ u, t ∈ dyadicSelectedCell e u
  · rw [selectedReadAtom, dif_pos h, single_apply]
    have hc := Classical.choose_spec h
    by_cases hs : t ∈ dyadicSelectedCell e s
    · have heq : Classical.choose h = s := by
        by_contra hne
        exact Finset.disjoint_left.mp (dyadicSelectedCell_disjoint e hne) hc hs
      simp [heq, hs]
    · have hne : Classical.choose h ≠ s := fun hcs => hs (hcs ▸ hc)
      simp only [if_neg hne, if_neg hs]
  · rw [selectedReadAtom, dif_neg h, zero_apply]
    exact (if_neg (fun hs => h ⟨s, hs⟩)).symm

def selectedReadLinear (e : DyadicSubtreeEmbedding) :
    JamesTreePreSpace 𝕜 p S →ₗ[𝕜] JamesTreePreSpace 𝕜 p S :=
  Finsupp.linearCombination 𝕜 (selectedReadAtom e)

theorem selectedReadLinear_single (e : DyadicSubtreeEmbedding) (t : DyadicTreeNode) (c : 𝕜) :
    selectedReadLinear (p := p) (S := S) e (single t c) = c • selectedReadAtom e t := by
  exact Finsupp.linearCombination_single 𝕜 c t

theorem selectedReadLinear_apply (e : DyadicSubtreeEmbedding)
    (a : JamesTreePreSpace 𝕜 p S) (s : DyadicTreeNode) :
    selectedReadLinear e a s = ∑ t ∈ dyadicSelectedCell e s, a t := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_apply, Finset.sum_const_zero]
  | add a b ha hb =>
    simp only [map_add, add_apply, ha, hb]
    exact Finset.sum_add_distrib.symm
  | single t c =>
    change selectedReadLinear e (single t c) s = ∑ u ∈ dyadicSelectedCell e s, single t c u
    rw [selectedReadLinear_single, smul_apply, selectedReadAtom_apply]
    simp [single_apply]

theorem selectedReadLinear_norm_le (e : DyadicSubtreeEmbedding)
    (hS : ∀ A, S.allows A → S.allows (dyadicSelectedCells e A))
    (a : JamesTreePreSpace 𝕜 p S) : ‖selectedReadLinear e a‖ ≤ ‖a‖ := by
  classical
  apply norm_le
  intro T
  let U : JamesTreeTest S := {
    count := T.count
    segment := fun j => dyadicSelectedCells e (T.segment j)
    allowed := fun j => hS _ (T.allowed j)
    disjoint := fun i j hij => dyadicSelectedCells_disjoint e (T.disjoint hij) }
  have htest : jamesTreeTestMap 𝕜 p T (coefficients (selectedReadLinear e a)) =
      jamesTreeTestMap 𝕜 p U a.coefficients := by
    ext j
    change (∑ s ∈ T.segment j, selectedReadLinear e a s) =
      ∑ t ∈ (T.segment j).biUnion (dyadicSelectedCell e), a t
    simp only [selectedReadLinear_apply]
    exact (Finset.sum_biUnion (fun s _ t _ hst => dyadicSelectedCell_disjoint e hst)).symm
  rw [htest]
  exact a.test_norm_le U

def selectedRead (e : DyadicSubtreeEmbedding)
    (hS : ∀ A, S.allows A → S.allows (dyadicSelectedCells e A)) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] JamesTreePreSpace 𝕜 p S :=
  (selectedReadLinear e).mkContinuous 1 (fun a => by
    simpa only [one_mul] using selectedReadLinear_norm_le e hS a)

theorem norm_selectedRead_le (e : DyadicSubtreeEmbedding)
    (hS : ∀ A, S.allows A → S.allows (dyadicSelectedCells e A)) :
    ‖selectedRead (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon.JamesTreePreSpace
