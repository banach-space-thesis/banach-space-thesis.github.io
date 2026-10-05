import ThesisCommon.Analysis.JamesTreePartialTests
import ThesisCommon.Analysis.JamesTreePrefixLinear
import ThesisCommon.Analysis.JamesTreePrefixPullback

/-! Contractive prefix insertion and reading on the actual finite-support
segment spaces. Both concrete segment conventions satisfy the structural
closure laws, proved independently of these analytic conclusions. -/
noncomputable section
namespace ThesisCommon

structure JamesTreePrefixClosure (S : JamesTreeSegmentFamily) (u : DyadicTreeNode) : Prop where
  forward : ∀ A, S.allows A → S.allows (A.map (dyadicPrefixEmbedding u))
  backward : ∀ A, S.allows A → (prefixPullback u A).Nonempty → S.allows (prefixPullback u A)

theorem literalJamesTreePrefixClosure (u : DyadicTreeNode) :
    JamesTreePrefixClosure literalTreeSegmentFamily u :=
  ⟨fun _ h => literalTreeSegment_prefix h u,
    fun _ h => literalTreeSegment_prefixPullback h u⟩

theorem consecutiveJamesTreePrefixClosure (u : DyadicTreeNode) :
    JamesTreePrefixClosure consecutiveTreeSegmentFamily u :=
  ⟨fun _ h => consecutiveTreeSegment_prefix h u,
    fun _ h => consecutiveTreeSegment_prefixPullback h u⟩

namespace JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem prefixInsertLinear_norm_le (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u)
    (a : JamesTreePreSpace 𝕜 p S) : ‖prefixInsertLinear u a‖ ≤ ‖a‖ := by
  classical
  apply norm_le
  intro T
  have heq : jamesTreeTestMap 𝕜 p T (coefficients (prefixInsertLinear u a)) =
      WithLp.toLp p.val (fun j => ∑ t ∈ prefixPullback u (T.segment j), a t) := by
    ext j
    exact sum_mapDomain_prefix u (T.segment j) a.coefficients
  rw [heq]
  exact jamesTree_partial_test_norm_le p a (fun j => prefixPullback u (T.segment j))
    (fun j hj => hS.backward _ (T.allowed j) hj)
    (fun _ _ hij => prefixPullback_disjoint u (T.disjoint hij))

def prefixInsert (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] JamesTreePreSpace 𝕜 p S :=
  (prefixInsertLinear u).mkContinuous 1 (fun a => by
    simpa only [one_mul] using prefixInsertLinear_norm_le u hS a)

@[simp] theorem prefixInsert_apply (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u)
    (a : JamesTreePreSpace 𝕜 p S) : prefixInsert u hS a = prefixInsertLinear u a := rfl

theorem norm_prefixInsert_le (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    ‖prefixInsert (𝕜 := 𝕜) (p := p) u hS‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem prefixRead_comp_insert (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    (prefixRead (𝕜 := 𝕜) (p := p) u hS.forward).comp (prefixInsert u hS) =
      ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro a
  exact DFunLike.congr_fun (prefixReadLinear_comp_insert u) a

theorem prefixInsert_norm (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u)
    (a : JamesTreePreSpace 𝕜 p S) : ‖prefixInsert u hS a‖ = ‖a‖ := by
  apply le_antisymm (prefixInsertLinear_norm_le u hS a)
  have h := prefixReadLinear_norm_le u hS.forward (prefixInsert u hS a)
  have heq := DFunLike.congr_fun (prefixRead_comp_insert (𝕜 := 𝕜) (p := p) u hS) a
  change prefixReadLinear u (prefixInsert u hS a) = a at heq
  rwa [heq] at h

end JamesTreePreSpace
end ThesisCommon
