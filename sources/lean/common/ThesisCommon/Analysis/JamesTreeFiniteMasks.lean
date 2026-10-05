import ThesisCommon.Analysis.JamesTreeCoordinates
import ThesisCommon.Analysis.JamesTreeMaskLimits
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite masks on the actual completion have precisely the finite spans
of their unit vectors as ranges. In particular their ranges are genuinely
finite dimensional; no finite-dimensionality is assumed in a model. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTree_dense_smul_unit (t : DyadicTreeNode) (c : 𝕜) :
    jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.single t c) =
      c • jamesTreeUnit t := by
  rw [jamesTreeUnit, ← map_smul]
  congr 1
  apply JamesTreePreSpace.ext
  intro u
  simp only [JamesTreePreSpace.single_apply, JamesTreePreSpace.smul_apply]
  split_ifs <;> simp

theorem jamesTreeMask_finite_sum (A : Finset DyadicTreeNode)
    (hA : JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeMask (A : Set DyadicTreeNode) hA x =
      ∑ t ∈ A, jamesTreeCoordinate t x • jamesTreeUnit t := by
  classical
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · apply isClosed_eq (jamesTreeMask (A : Set DyadicTreeNode) hA).continuous
    exact continuous_finset_sum _ (fun t _ => (jamesTreeCoordinate t).continuous.smul continuous_const)
  · intro a
    rw [jamesTreeMask_dense]
    simp only [jamesTreeCoordinate_dense]
    have heq : JamesTreePreSpace.mask (A : Set DyadicTreeNode) hA a =
        ∑ t ∈ A, JamesTreePreSpace.single t (a t) := by
      apply JamesTreePreSpace.ext
      intro u
      change (JamesTreePreSpace.coordinate u) (JamesTreePreSpace.mask (A : Set DyadicTreeNode) hA a) =
        (JamesTreePreSpace.coordinate u) (∑ t ∈ A, JamesTreePreSpace.single t (a t))
      rw [map_sum]
      simp [JamesTreePreSpace.coordinate_apply, JamesTreePreSpace.mask_apply,
        JamesTreePreSpace.single_apply, eq_comm]
    rw [heq, map_sum]
    exact Finset.sum_congr rfl (fun t _ => jamesTree_dense_smul_unit t (a t))

def jamesTreeFiniteSpan (A : Finset DyadicTreeNode) : Submodule 𝕜 (SegmentJamesTreeSpace 𝕜 p S) :=
  Submodule.span 𝕜 (jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) '' (A : Set DyadicTreeNode))

instance jamesTreeFiniteSpan_finiteDimensional (A : Finset DyadicTreeNode) :
    FiniteDimensional 𝕜 (jamesTreeFiniteSpan (𝕜 := 𝕜) (p := p) (S := S) A) :=
  FiniteDimensional.span_of_finite 𝕜 (A.finite_toSet.image _)

theorem jamesTreeMask_unit (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    {t : DyadicTreeNode} (ht : t ∈ A) :
    jamesTreeMask (𝕜 := 𝕜) (p := p) A hA (jamesTreeUnit t) = jamesTreeUnit t := by
  apply jamesTreeMask_fix_dense
  intro u hu
  have htu : t ≠ u := fun heq => hu (heq ▸ ht)
  simp only [JamesTreePreSpace.single_apply, if_neg htu]

theorem jamesTreeMask_range_eq_finiteSpan (A : Finset DyadicTreeNode)
    (hA : JamesTreeMaskClosed S (A : Set DyadicTreeNode)) :
    LinearMap.range (jamesTreeMask (𝕜 := 𝕜) (p := p) (A : Set DyadicTreeNode) hA).toLinearMap =
      jamesTreeFiniteSpan A := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change jamesTreeMask (A : Set DyadicTreeNode) hA x ∈ jamesTreeFiniteSpan A
    rw [jamesTreeMask_finite_sum]
    exact Submodule.sum_mem _ (fun t ht => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨t, ht, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨jamesTreeUnit t, jamesTreeMask_unit (A : Set DyadicTreeNode) hA ht⟩

theorem jamesTreeMask_finiteDimensional_range (A : Finset DyadicTreeNode)
    (hA : JamesTreeMaskClosed S (A : Set DyadicTreeNode)) :
    FiniteDimensional 𝕜
      (LinearMap.range (jamesTreeMask (𝕜 := 𝕜) (p := p) (A : Set DyadicTreeNode) hA).toLinearMap) := by
  rw [jamesTreeMask_range_eq_finiteSpan]
  infer_instance

end ThesisCommon
