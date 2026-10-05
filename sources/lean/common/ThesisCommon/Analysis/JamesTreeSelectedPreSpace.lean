import ThesisCommon.Analysis.JamesTreeSelectedRead
import ThesisCommon.Analysis.JamesTreeSelectedPullback
import ThesisCommon.Analysis.JamesTreePartialTests
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Actual selected-subtree insertion and cell readback. The hypotheses below
are purely geometric segment closure, and are proved for each convention. -/
noncomputable section
namespace ThesisCommon

structure JamesTreeSelectedClosure (S : JamesTreeSegmentFamily)
    (e : DyadicSubtreeEmbedding) : Prop where
  cells : ∀ A, S.allows A → S.allows (dyadicSelectedCells e A)
  backward : ∀ A, S.allows A → (selectedPullback e A).Nonempty →
    S.allows (selectedPullback e A)

theorem literalJamesTreeSelectedClosure (e : DyadicSubtreeEmbedding) :
    JamesTreeSelectedClosure literalTreeSegmentFamily e :=
  ⟨fun _ h => dyadicSelectedCells_literal e h,
    fun _ h => literalTreeSegment_selectedPullback h e⟩

theorem consecutiveJamesTreeSelectedClosure (e : DyadicSubtreeEmbedding) :
    JamesTreeSelectedClosure consecutiveTreeSegmentFamily e :=
  ⟨fun _ h => dyadicSelectedCells_consecutive e h,
    fun _ h => consecutiveTreeSegment_selectedPullback h e⟩

namespace JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def selectedInsertLinear (e : DyadicSubtreeEmbedding) :
    JamesTreePreSpace 𝕜 p S →ₗ[𝕜] JamesTreePreSpace 𝕜 p S :=
  Finsupp.lmapDomain 𝕜 𝕜 e.toEmbedding

@[simp] theorem selectedInsertLinear_apply_image (e : DyadicSubtreeEmbedding)
    (t : DyadicTreeNode) (a : JamesTreePreSpace 𝕜 p S) :
    selectedInsertLinear e a (e t) = a t :=
  Finsupp.mapDomain_apply e.toEmbedding.injective a t

theorem selectedInsertLinear_apply_of_not_mem (e : DyadicSubtreeEmbedding)
    (t : DyadicTreeNode) (a : JamesTreePreSpace 𝕜 p S) (ht : t ∉ Set.range e) :
    selectedInsertLinear e a t = 0 :=
  Finsupp.mapDomain_notin_range a t ht

theorem selectedInsertLinear_norm_le (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    ‖selectedInsertLinear e a‖ ≤ ‖a‖ := by
  classical
  apply norm_le
  intro T
  have heq : jamesTreeTestMap 𝕜 p T (coefficients (selectedInsertLinear e a)) =
      WithLp.toLp p.val (fun j => ∑ t ∈ selectedPullback e (T.segment j), a t) := by
    ext j
    exact sum_mapDomain_selected e (T.segment j) a.coefficients
  rw [heq]
  exact jamesTree_partial_test_norm_le p a (fun j => selectedPullback e (T.segment j))
    (fun j hj => hS.backward _ (T.allowed j) hj)
    (fun _ _ hij => selectedPullback_disjoint e (T.disjoint hij))

def selectedInsert (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] JamesTreePreSpace 𝕜 p S :=
  (selectedInsertLinear e).mkContinuous 1 (fun a => by
    simpa only [one_mul] using selectedInsertLinear_norm_le e hS a)

@[simp] theorem selectedInsert_apply (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    selectedInsert e hS a = selectedInsertLinear e a := rfl

theorem norm_selectedInsert_le (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    ‖selectedInsert (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem selectedReadLinear_insert (e : DyadicSubtreeEmbedding)
    (a : JamesTreePreSpace 𝕜 p S) :
    selectedReadLinear e (selectedInsertLinear e a) = a := by
  classical
  apply ext
  intro s
  rw [selectedReadLinear_apply]
  change (∑ t ∈ dyadicSelectedCell e s, (Finsupp.mapDomain e.toEmbedding a) t) = a s
  rw [sum_mapDomain_selected, selectedPullback_cell, Finset.sum_singleton]
  rfl

theorem selectedRead_comp_insert (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    (selectedRead (𝕜 := 𝕜) (p := p) e hS.cells).comp (selectedInsert e hS) =
      ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro a
  exact selectedReadLinear_insert e a

theorem selectedInsert_norm (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    ‖selectedInsert e hS a‖ = ‖a‖ := by
  apply le_antisymm (selectedInsertLinear_norm_le e hS a)
  have h := selectedReadLinear_norm_le e hS.cells (selectedInsert e hS a)
  have heq := selectedReadLinear_insert e a
  change selectedReadLinear e (selectedInsert e hS a) = a at heq
  rwa [heq] at h

end JamesTreePreSpace
end ThesisCommon
