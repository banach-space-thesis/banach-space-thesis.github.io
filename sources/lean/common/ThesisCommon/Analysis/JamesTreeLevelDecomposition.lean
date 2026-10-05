import ThesisCommon.Analysis.JamesTreeFiniteLevels
import Mathlib.LinearAlgebra.Basis.Basic

/-! Genuine finite coordinate bases, compatible level projections and
vanishing tails for both completed James-tree models. No unconditionality
of arbitrary masks in the consecutive model is asserted. -/
noncomputable section
open Filter Topology Module
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTreeFiniteSpan_eq_span_range (A : Finset DyadicTreeNode) :
    Submodule.span 𝕜 (Set.range (fun t : A =>
      jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) t.val)) = jamesTreeFiniteSpan A := by
  apply congrArg (Submodule.span 𝕜)
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.val, t.property, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

def jamesTreeFiniteBasis (A : Finset DyadicTreeNode) :
    Basis A 𝕜 (jamesTreeFiniteSpan (𝕜 := 𝕜) (p := p) (S := S) A) :=
  (Basis.span ((jamesTreeUnit_linearIndependent (𝕜 := 𝕜) (p := p) (S := S)).comp
    (fun t : A => t.val) Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ (jamesTreeFiniteSpan_eq_span_range A))

@[simp] theorem jamesTreeFiniteBasis_apply (A : Finset DyadicTreeNode) (t : A) :
    ((jamesTreeFiniteBasis (𝕜 := 𝕜) (p := p) (S := S) A) t :
      SegmentJamesTreeSpace 𝕜 p S) = jamesTreeUnit t.val := by
  simp only [jamesTreeFiniteBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply,
    Function.comp_apply]

theorem jamesTreeFiniteSpan_finrank (A : Finset DyadicTreeNode) :
    Module.finrank 𝕜 (jamesTreeFiniteSpan (𝕜 := 𝕜) (p := p) (S := S) A) = A.card := by
  rw [Module.finrank_eq_card_basis (jamesTreeFiniteBasis (𝕜 := 𝕜) (p := p) (S := S) A)]
  exact Fintype.card_coe A

theorem jamesTreeMask_comp_of_subset
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (A B : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    (hB : JamesTreeMaskClosed S B) (hAB : A ⊆ B) :
    (jamesTreeMask (𝕜 := 𝕜) (p := p) A hA).comp (jamesTreeMask B hB) =
      jamesTreeMask A hA := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply jamesTreeCoordinate_ext hS
  intro t
  simp only [ContinuousLinearMap.comp_apply, jamesTreeCoordinate_mask]
  by_cases ht : t ∈ A
  · simp only [if_pos ht, if_pos (hAB ht)]
  · simp only [if_neg ht]

theorem jamesTreeLevelProjection_comp_min
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)) (M N : ℕ) :
    (jamesTreeMask (𝕜 := 𝕜) (p := p) (dyadicInitialLevels M) (hS M)).comp
      (jamesTreeMask (dyadicInitialLevels N) (hS N)) =
      jamesTreeMask (dyadicInitialLevels (min M N)) (hS (min M N)) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply jamesTreeCoordinate_ext hS
  intro t
  simp only [ContinuousLinearMap.comp_apply, jamesTreeCoordinate_mask,
    dyadicInitialLevels, Set.mem_setOf_eq, Nat.le_min]
  by_cases hM : t.length ≤ M <;> by_cases hN : t.length ≤ N <;> simp [hM, hN]

theorem literalJamesTreeLevelProjection_comp_min (p : BanachExponent) (M N : ℕ) :
    (literalJamesTreeLevelProjection (𝕜 := 𝕜) p M).comp (literalJamesTreeLevelProjection p N) =
      literalJamesTreeLevelProjection p (min M N) :=
  jamesTreeLevelProjection_comp_min literalJamesTreeMaskClosed_levels M N

theorem consecutiveJamesTreeLevelProjection_comp_min (p : BanachExponent) (M N : ℕ) :
    (consecutiveJamesTreeLevelProjection (𝕜 := 𝕜) p M).comp (consecutiveJamesTreeLevelProjection p N) =
      consecutiveJamesTreeLevelProjection p (min M N) :=
  jamesTreeLevelProjection_comp_min consecutiveJamesTreeMaskClosed_levels M N

theorem jamesTreeLevelTail_norm_le (N : ℕ)
    (hN : JamesTreeMaskClosed S (dyadicInitialLevels N)) :
    ‖ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) -
      jamesTreeMask (dyadicInitialLevels N) hN‖ ≤ 2 := by
  calc
    _ ≤ ‖ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S)‖ +
        ‖jamesTreeMask (𝕜 := 𝕜) (p := p) (dyadicInitialLevels N) hN‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add ContinuousLinearMap.norm_id_le (norm_jamesTreeMask_le _ _)
    _ = 2 := by norm_num

theorem jamesTreeLevelTail_tendsto
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    Tendsto (fun N => x - jamesTreeMask (dyadicInitialLevels N) (hS N) x) atTop (𝓝 0) := by
  simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub
    (jamesTreeMask_tendsto dyadicInitialLevels hS (fun t => eventually_ge_atTop t.length) x)

end ThesisCommon
