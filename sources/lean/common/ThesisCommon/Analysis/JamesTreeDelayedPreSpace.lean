import ThesisCommon.Analysis.JamesTreeDelayedRead
import ThesisCommon.Analysis.JamesTreeSelectedPullback
import ThesisCommon.Analysis.JamesTreePartialTests
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Actual selected-subtree insertion and cell readback. The hypotheses below
are purely geometric segment closure, and are proved for each convention. -/
noncomputable section
namespace ThesisCommon

theorem sum_mapDomain_delayed {𝕜 : Type*} [AddCommMonoid 𝕜]
    (e : DyadicDelayedFork) (A : Finset DyadicTreeNode) (a : DyadicTreeNode →₀ 𝕜) :
    ∑ t ∈ A, (Finsupp.mapDomain e.nodeEmbedding a) t = ∑ t ∈ e.pullback A, a t := by
  classical
  have h := Finset.sum_preimage e.nodeEmbedding A e.nodeEmbedding.injective.injOn
    (Finsupp.mapDomain e.nodeEmbedding a)
    (fun t _ ht => Finsupp.mapDomain_notin_range a t ht)
  simpa only [DyadicDelayedFork.pullback, Finsupp.mapDomain_apply e.nodeEmbedding.injective]
    using h.symm

structure JamesTreeDelayedForkClosure (S : JamesTreeSegmentFamily)
    (e : DyadicDelayedFork) : Prop where
  cells : ∀ A, S.allows A → S.allows (dyadicRootedCells e.fork A)
  backward : ∀ A, S.allows A → (e.pullback A).Nonempty →
    S.allows (e.pullback A)

theorem literalJamesTreeDelayedForkClosure (e : DyadicDelayedFork) :
    JamesTreeDelayedForkClosure literalTreeSegmentFamily e :=
  ⟨fun _ h => dyadicRootedCells_literal e.fork h,
    fun _ h => e.pullback_literal h⟩

theorem consecutiveJamesTreeDelayedForkClosure (e : DyadicDelayedFork) :
    JamesTreeDelayedForkClosure consecutiveTreeSegmentFamily e :=
  ⟨fun _ h => dyadicRootedCells_consecutive e.fork h,
    fun _ h => e.pullback_consecutive h⟩

namespace JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def delayedInsertLinear (e : DyadicDelayedFork) :
    JamesTreePreSpace 𝕜 p S →ₗ[𝕜] JamesTreePreSpace 𝕜 p S :=
  Finsupp.lmapDomain 𝕜 𝕜 e.nodeEmbedding

@[simp] theorem delayedInsertLinear_apply_image (e : DyadicDelayedFork)
    (t : DyadicTreeNode) (a : JamesTreePreSpace 𝕜 p S) :
    delayedInsertLinear e a (e.node t) = a t :=
  Finsupp.mapDomain_apply e.nodeEmbedding.injective a t

theorem delayedInsertLinear_apply_of_not_mem (e : DyadicDelayedFork)
    (t : DyadicTreeNode) (a : JamesTreePreSpace 𝕜 p S) (ht : t ∉ Set.range e.node) :
    delayedInsertLinear e a t = 0 :=
  Finsupp.mapDomain_notin_range a t ht

theorem delayedInsertLinear_norm_le (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    ‖delayedInsertLinear e a‖ ≤ ‖a‖ := by
  classical
  apply norm_le
  intro T
  have heq : jamesTreeTestMap 𝕜 p T (coefficients (delayedInsertLinear e a)) =
      WithLp.toLp p.val (fun j => ∑ t ∈ e.pullback (T.segment j), a t) := by
    ext j
    exact sum_mapDomain_delayed e (T.segment j) a.coefficients
  rw [heq]
  exact jamesTree_partial_test_norm_le p a (fun j => e.pullback (T.segment j))
    (fun j hj => hS.backward _ (T.allowed j) hj)
    (fun _ _ hij => e.pullback_disjoint (T.disjoint hij))

def delayedInsert (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] JamesTreePreSpace 𝕜 p S :=
  (delayedInsertLinear e).mkContinuous 1 (fun a => by
    simpa only [one_mul] using delayedInsertLinear_norm_le e hS a)

@[simp] theorem delayedInsert_apply (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    delayedInsert e hS a = delayedInsertLinear e a := rfl

theorem norm_delayedInsert_le (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    ‖delayedInsert (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem delayedReadLinear_insert (e : DyadicDelayedFork)
    (a : JamesTreePreSpace 𝕜 p S) :
    delayedReadLinear e (delayedInsertLinear e a) = a := by
  classical
  apply ext
  intro s
  rw [delayedReadLinear_apply]
  change (∑ t ∈ dyadicRootedCell e.fork s, (Finsupp.mapDomain e.nodeEmbedding a) t) = a s
  rw [sum_mapDomain_delayed, DyadicDelayedFork.pullback_cell, Finset.sum_singleton]
  rfl

theorem delayedRead_comp_insert (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    (delayedRead (𝕜 := 𝕜) (p := p) e hS.cells).comp (delayedInsert e hS) =
      ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro a
  exact delayedReadLinear_insert e a

theorem delayedInsert_norm (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    ‖delayedInsert e hS a‖ = ‖a‖ := by
  apply le_antisymm (delayedInsertLinear_norm_le e hS a)
  have h := delayedReadLinear_norm_le e hS.cells (delayedInsert e hS a)
  have heq := delayedReadLinear_insert e a
  change delayedReadLinear e (delayedInsert e hS a) = a at heq
  rwa [heq] at h

end JamesTreePreSpace
end ThesisCommon
