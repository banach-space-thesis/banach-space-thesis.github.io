import ThesisCommon.Analysis.JamesTreeFiniteLevels
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Actual norm-one chain functionals on both James-tree completions.
The literal model permits arbitrary chains; the consecutive model requires
order-convex chains. Their finite initial-level intersections are genuine
allowed segments, which proves the bound before extending by density. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

def IsTreeChain (B : Set DyadicTreeNode) : Prop :=
  ∀ s ∈ B, ∀ t ∈ B, s.IsPrefix t ∨ t.IsPrefix s

def IsConvexTreeChain (B : Set DyadicTreeNode) : Prop :=
  IsTreeChain B ∧ ∀ s ∈ B, ∀ t ∈ B, ∀ u, s.IsPrefix u → u.IsPrefix t → u ∈ B

def JamesTreeChainClosed (S : JamesTreeSegmentFamily) (B : Set DyadicTreeNode) : Prop :=
  ∀ N, ((dyadicInitialFinset N).filter (· ∈ B)).Nonempty →
    S.allows ((dyadicInitialFinset N).filter (· ∈ B))

theorem literalJamesTreeChainClosed {B : Set DyadicTreeNode} (hB : IsTreeChain B) :
    JamesTreeChainClosed literalTreeSegmentFamily B := by
  intro N hN
  refine ⟨hN, ?_⟩
  intro s hs t ht
  exact hB s (Finset.mem_filter.mp hs).2 t (Finset.mem_filter.mp ht).2

theorem consecutiveJamesTreeChainClosed {B : Set DyadicTreeNode}
    (hB : IsConvexTreeChain B) : JamesTreeChainClosed consecutiveTreeSegmentFamily B := by
  intro N hN
  refine ⟨literalJamesTreeChainClosed hB.1 N hN, ?_⟩
  intro s hs t ht u hsu hut
  obtain ⟨hsN, hsB⟩ := Finset.mem_filter.mp hs
  obtain ⟨htN, htB⟩ := Finset.mem_filter.mp ht
  refine Finset.mem_filter.mpr ⟨?_, hB.2 s hsB t htB u hsu hut⟩
  exact (mem_dyadicInitialFinset u N).mpr
    (hut.length_le.trans ((mem_dyadicInitialFinset t N).mp htN))

namespace JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def chainSumLinear (B : Set DyadicTreeNode) : JamesTreePreSpace 𝕜 p S →ₗ[𝕜] 𝕜 :=
  Finsupp.linearCombination 𝕜 (fun t => if t ∈ B then (1 : 𝕜) else 0)

theorem chainSumLinear_eq_initial_sum (B : Set DyadicTreeNode)
    (a : JamesTreePreSpace 𝕜 p S) (N : ℕ)
    (ha : ∀ t ∈ a.coefficients.support, t.length ≤ N) :
    chainSumLinear B a = ∑ t ∈ (dyadicInitialFinset N).filter (· ∈ B), a t := by
  have hs : a.coefficients ∈ Finsupp.supported 𝕜 𝕜
      ((dyadicInitialFinset N : Finset DyadicTreeNode) : Set DyadicTreeNode) := by
    intro t ht
    exact (mem_dyadicInitialFinset t N).mpr (ha t ht)
  change Finsupp.linearCombination 𝕜 (fun t => if t ∈ B then (1 : 𝕜) else 0)
      a.coefficients = _
  rw [Finsupp.linearCombination_apply_of_mem_supported 𝕜 hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp

theorem chainSumLinear_norm_le (B : Set DyadicTreeNode) (hB : JamesTreeChainClosed S B)
    (a : JamesTreePreSpace 𝕜 p S) : ‖chainSumLinear B a‖ ≤ ‖a‖ := by
  let N := a.coefficients.support.sup List.length
  have ha : ∀ t ∈ a.coefficients.support, t.length ≤ N :=
    fun t ht => Finset.le_sup ht
  rw [chainSumLinear_eq_initial_sum B a N ha]
  let A := (dyadicInitialFinset N).filter (· ∈ B)
  have htest := jamesTree_partial_test_norm_le p a (fun _ : Fin 1 => A)
    (fun _ => hB N) (fun i j hij => (hij (Subsingleton.elim i j)).elim)
  exact (PiLp.norm_apply_le (WithLp.toLp p.val
    (fun _ : Fin 1 => ∑ t ∈ A, a t)) (0 : Fin 1)).trans htest

def chainFunctional (B : Set DyadicTreeNode) (hB : JamesTreeChainClosed S B) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] 𝕜 :=
  (chainSumLinear B).mkContinuous 1 (fun a => by
    simpa only [one_mul] using chainSumLinear_norm_le B hB a)

@[simp] theorem chainFunctional_single (B : Set DyadicTreeNode)
    (hB : JamesTreeChainClosed S B) (t : DyadicTreeNode) (c : 𝕜) :
    chainFunctional (p := p) B hB (single t c) = if t ∈ B then c else 0 := by
  change Finsupp.linearCombination 𝕜 (fun t => if t ∈ B then (1 : 𝕜) else 0)
    (Finsupp.single t c) = _
  rw [Finsupp.linearCombination_single]
  split_ifs <;> simp

end JamesTreePreSpace

variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeChainFunctional (B : Set DyadicTreeNode) (hB : JamesTreeChainClosed S B) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] 𝕜 :=
  (JamesTreePreSpace.chainFunctional B hB).extend
    (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
    (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
    (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

@[simp] theorem jamesTreeChainFunctional_dense (B : Set DyadicTreeNode)
    (hB : JamesTreeChainClosed S B) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreeChainFunctional B hB (jamesTreeDenseEmbedding 𝕜 p S a) =
      JamesTreePreSpace.chainSumLinear B a :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

theorem jamesTreeChainFunctional_norm_le (B : Set DyadicTreeNode)
    (hB : JamesTreeChainClosed S B) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreeChainFunctional B hB x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeChainFunctional B hB).continuous.norm continuous_norm
  · intro a
    rw [jamesTreeChainFunctional_dense, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.chainSumLinear_norm_le B hB a

theorem norm_jamesTreeChainFunctional_le (B : Set DyadicTreeNode)
    (hB : JamesTreeChainClosed S B) :
    ‖jamesTreeChainFunctional (𝕜 := 𝕜) (p := p) B hB‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using jamesTreeChainFunctional_norm_le B hB x

@[simp] theorem jamesTreeChainFunctional_unit (B : Set DyadicTreeNode)
    (hB : JamesTreeChainClosed S B) (t : DyadicTreeNode) :
    jamesTreeChainFunctional (𝕜 := 𝕜) (p := p) B hB (jamesTreeUnit t) =
      if t ∈ B then 1 else 0 := by
  change jamesTreeChainFunctional B hB
    (jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.single t 1)) = _
  rw [jamesTreeChainFunctional_dense]
  exact JamesTreePreSpace.chainFunctional_single B hB t 1

theorem norm_jamesTreeChainFunctional (B : Set DyadicTreeNode)
    (hB : JamesTreeChainClosed S B) (hne : B.Nonempty) :
    ‖jamesTreeChainFunctional (𝕜 := 𝕜) (p := p) B hB‖ = 1 := by
  apply le_antisymm (norm_jamesTreeChainFunctional_le B hB)
  obtain ⟨t, ht⟩ := hne
  have h := (jamesTreeChainFunctional (𝕜 := 𝕜) (p := p) B hB).le_opNorm (jamesTreeUnit t)
  simpa only [jamesTreeChainFunctional_unit, if_pos ht, norm_one, norm_jamesTreeUnit,
    mul_one] using h

end ThesisCommon
