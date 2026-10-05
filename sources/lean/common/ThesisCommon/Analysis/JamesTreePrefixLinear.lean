import ThesisCommon.Analysis.JamesTreePrefixSegments
import ThesisCommon.Analysis.JamesTreeSpace
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Concrete finite-support insertion and reading for a genuine prefix
subtree. Reading is contractive whenever prefix images preserve segments. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def prefixInsertLinear (u : DyadicTreeNode) :
    JamesTreePreSpace 𝕜 p S →ₗ[𝕜] JamesTreePreSpace 𝕜 p S :=
  Finsupp.lmapDomain 𝕜 𝕜 (dyadicPrefixEmbedding u)

def prefixReadLinear (u : DyadicTreeNode) :
    JamesTreePreSpace 𝕜 p S →ₗ[𝕜] JamesTreePreSpace 𝕜 p S :=
  Finsupp.lcomapDomain (R := 𝕜) (M := 𝕜)
    (dyadicPrefixEmbedding u) (dyadicPrefixEmbedding u).injective

@[simp] theorem prefixReadLinear_apply (u t : DyadicTreeNode)
    (a : JamesTreePreSpace 𝕜 p S) : prefixReadLinear u a t = a (u ++ t) := rfl

@[simp] theorem prefixInsertLinear_apply_image (u t : DyadicTreeNode)
    (a : JamesTreePreSpace 𝕜 p S) : prefixInsertLinear u a (u ++ t) = a t := by
  exact Finsupp.mapDomain_apply (dyadicPrefixEmbedding u).injective a t

theorem prefixInsertLinear_apply_of_not_prefix (u t : DyadicTreeNode)
    (a : JamesTreePreSpace 𝕜 p S) (h : ¬ u.IsPrefix t) : prefixInsertLinear u a t = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨s, hs⟩
  exact h ⟨s, hs⟩

theorem prefixReadLinear_comp_insert (u : DyadicTreeNode) :
    (prefixReadLinear (𝕜 := 𝕜) (p := p) (S := S) u).comp (prefixInsertLinear u) =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply ext
  intro t
  exact prefixInsertLinear_apply_image u t a

theorem prefixReadLinear_norm_le (u : DyadicTreeNode)
    (hS : ∀ A, S.allows A → S.allows (A.map (dyadicPrefixEmbedding u)))
    (a : JamesTreePreSpace 𝕜 p S) : ‖prefixReadLinear u a‖ ≤ ‖a‖ := by
  classical
  apply norm_le
  intro T
  have heq : jamesTreeTestMap 𝕜 p T (coefficients (prefixReadLinear u a)) =
      jamesTreeTestMap 𝕜 p (T.prefix u hS) (coefficients a) := by
    ext j
    change (∑ t ∈ T.segment j, a (u ++ t)) =
      ∑ t ∈ (T.segment j).map (dyadicPrefixEmbedding u), a t
    simp only [Finset.sum_map, dyadicPrefixEmbedding_apply]
  rw [heq]
  exact a.test_norm_le (T.prefix u hS)

def prefixRead (u : DyadicTreeNode)
    (hS : ∀ A, S.allows A → S.allows (A.map (dyadicPrefixEmbedding u))) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] JamesTreePreSpace 𝕜 p S :=
  (prefixReadLinear u).mkContinuous 1 (fun a => by
    simpa only [one_mul] using prefixReadLinear_norm_le u hS a)

@[simp] theorem prefixRead_apply (u : DyadicTreeNode) (hS)
    (a : JamesTreePreSpace 𝕜 p S) : prefixRead u hS a = prefixReadLinear u a := rfl

theorem norm_prefixRead_le (u : DyadicTreeNode) (hS) :
    ‖prefixRead (𝕜 := 𝕜) (p := p) (S := S) u hS‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon.JamesTreePreSpace
