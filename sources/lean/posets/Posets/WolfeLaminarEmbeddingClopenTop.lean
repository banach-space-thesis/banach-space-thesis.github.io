import Posets.WolfeLaminarEmbedding
import Mathlib.Topology.Algebra.Support

/-! The laminar quotient embedding for a compact clopen top cell.

Functions on the top cell are extended by zero into the original ambient
space.  The resulting isometry sends the quotient coordinates to the
original ambient indicator functions.
-/

noncomputable section
open Set Filter Topology

namespace Posets

variable {𝕜 K ι : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
variable (H : Set K) [CompactSpace H]

/-- Actual zero extension from a compact clopen subspace. -/
def wolfeClopenZeroExtend (hH : IsClopen H) (f : C(H, 𝕜)) : JLMS.CZero 𝕜 K where
  toFun := Function.extend Subtype.val f 0
  continuous_toFun := HasCompactSupport.continuous_extend_zero hH.isOpen f.continuous
    (HasCompactSupport.of_compactSpace f)
  zero_at_infty' := ((HasCompactSupport.of_compactSpace f).extend_zero
    continuous_subtype_val).is_zero_at_infty

@[simp] theorem wolfeClopenZeroExtend_apply_mem (hH : IsClopen H)
    (f : C(H, 𝕜)) (x : H) : wolfeClopenZeroExtend H hH f x = f x :=
  Function.Injective.extend_apply Subtype.val_injective _ _ _

@[simp] theorem wolfeClopenZeroExtend_apply_notMem (hH : IsClopen H)
    (f : C(H, 𝕜)) {x : K} (hx : x ∉ H) : wolfeClopenZeroExtend H hH f x = 0 := by
  exact Function.extend_apply' _ _ _ (by simpa using hx)

/-- Zero extension preserves the supremum norm exactly. -/
def wolfeClopenZeroExtension (hH : IsClopen H) : C(H, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K where
  toFun := wolfeClopenZeroExtend H hH
  map_add' f g := by
    ext x
    by_cases hx : x ∈ H
    · exact (wolfeClopenZeroExtend_apply_mem H hH (f + g) ⟨x, hx⟩).trans (by
        simp only [ContinuousMap.add_apply, ZeroAtInftyContinuousMap.add_apply]
        rw [wolfeClopenZeroExtend_apply_mem H hH f ⟨x, hx⟩,
          wolfeClopenZeroExtend_apply_mem H hH g ⟨x, hx⟩])
    · simp [hx]
  map_smul' a f := by
    ext x
    by_cases hx : x ∈ H
    · exact (wolfeClopenZeroExtend_apply_mem H hH (a • f) ⟨x, hx⟩).trans (by
        simp only [ContinuousMap.smul_apply, ZeroAtInftyContinuousMap.smul_apply]
        rw [wolfeClopenZeroExtend_apply_mem H hH f ⟨x, hx⟩]
        rfl)
    · simp [hx]
  norm_map' f := by
    apply le_antisymm
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
      intro x
      change ‖wolfeClopenZeroExtend H hH f x‖ ≤ ‖f‖
      by_cases hx : x ∈ H
      · rw [wolfeClopenZeroExtend_apply_mem H hH f ⟨x, hx⟩]
        exact f.norm_coe_le_norm _
      · rw [wolfeClopenZeroExtend_apply_notMem H hH f hx, norm_zero]
        exact norm_nonneg f
    · apply (ContinuousMap.norm_le f (norm_nonneg _)).mpr
      intro x
      rw [← wolfeClopenZeroExtend_apply_mem H hH f x]
      exact JLMS.norm_CZero_apply_le _ _

/-- The family of cells as subsets of the top cell. -/
def wolfeClopenTopCells (A : ι → Set K) : ι → Set H :=
  fun i => Subtype.val ⁻¹' A i

omit [T2Space K] [CompactSpace H] in
theorem wolfeClopenTopCells_isClopen (A : ι → Set K) (hA : ∀ i, IsClopen (A i))
    (i : ι) : IsClopen (wolfeClopenTopCells H A i) :=
  (hA i).preimage continuous_subtype_val

omit [TopologicalSpace K] [T2Space K] [CompactSpace H] in
theorem wolfeClopenTopCells_unit (A : ι → Set K) (hunit : ∃ i, A i = H) :
    ∃ i, wolfeClopenTopCells H A i = univ := by
  obtain ⟨i, hi⟩ := hunit
  exact ⟨i, by ext x; simp [wolfeClopenTopCells, hi]⟩

omit [TopologicalSpace K] [T2Space K] [CompactSpace H] in
theorem wolfeClopenTopCells_laminar (A : ι → Set K)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j)) :
    ∀ i j, wolfeClopenTopCells H A i ⊆ wolfeClopenTopCells H A j ∨
      wolfeClopenTopCells H A j ⊆ wolfeClopenTopCells H A i ∨
      Disjoint (wolfeClopenTopCells H A i) (wolfeClopenTopCells H A j) := by
  intro i j
  rcases hlam i j with h | h | h
  · exact Or.inl (preimage_mono h)
  · exact Or.inr (Or.inl (preimage_mono h))
  · exact Or.inr (Or.inr (h.preimage Subtype.val))

/-- The membership quotient of the top cell, omitting the ambient complement. -/
abbrev WolfeClopenTopQuotient (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) :=
  WolfeClopenQuotient (wolfeClopenTopCells H A) (wolfeClopenTopCells_isClopen H A hA)

/-- Pullback on the top-cell quotient followed by actual ambient zero extension. -/
def wolfeClopenTopIsometry (hH : IsClopen H) (A : ι → Set K)
    (hA : ∀ i, IsClopen (A i)) :
    C(WolfeClopenTopQuotient H A hA, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K :=
  (wolfeClopenZeroExtension H hH).comp
    (wolfeClopenPullIsometry (wolfeClopenTopCells H A) (wolfeClopenTopCells_isClopen H A hA))

/-- Every quotient coordinate becomes its original ambient indicator. -/
theorem wolfeClopenTopIsometry_coordinate (hH : IsClopen H) (A : ι → Set K)
    (hA : ∀ i, IsClopen (A i)) (hcA : ∀ i, IsCompact (A i))
    (hAH : ∀ i, A i ⊆ H) (i : ι) :
    wolfeClopenTopIsometry (𝕜 := 𝕜) H hH A hA
      (wolfeClopenCoordinate (wolfeClopenTopCells H A) (wolfeClopenTopCells_isClopen H A hA) i) =
      JLMS.clopenIndicator (A i) (hA i) (hcA i) := by
  classical
  ext x
  change wolfeClopenZeroExtend H hH
    (wolfeClopenPullIsometry (𝕜 := 𝕜) (wolfeClopenTopCells H A)
      (wolfeClopenTopCells_isClopen H A hA)
      (wolfeClopenCoordinate (𝕜 := 𝕜) (wolfeClopenTopCells H A)
        (wolfeClopenTopCells_isClopen H A hA) i)) x = _
  by_cases hx : x ∈ H
  · rw [wolfeClopenZeroExtend_apply_mem H hH _ ⟨x, hx⟩]
    change wolfeClopenCoordinate (𝕜 := 𝕜) (wolfeClopenTopCells H A)
      (wolfeClopenTopCells_isClopen H A hA) i
      (wolfeClopenProjection (wolfeClopenTopCells H A)
        (wolfeClopenTopCells_isClopen H A hA) ⟨x, hx⟩) = _
    rw [wolfeClopenCoordinate_projection, JLMS.clopenIndicator_apply]
    by_cases hi : x ∈ A i
    · rw [Set.indicator_of_mem (show (⟨x, hx⟩ : H) ∈ wolfeClopenTopCells H A i from hi), if_pos hi]
    · rw [Set.indicator_of_notMem (show (⟨x, hx⟩ : H) ∉ wolfeClopenTopCells H A i from hi), if_neg hi]
  · rw [wolfeClopenZeroExtend_apply_notMem H hH _ hx, JLMS.clopenIndicator_apply]
    simp [show x ∉ A i from fun h => hx (hAH i h)]

/-- The top-cell quotient gives exactly the closed span of the original indicators. -/
theorem wolfeClopenTopIsometry_range (hH : IsClopen H) (A : ι → Set K)
    (hA : ∀ i, IsClopen (A i)) (hcA : ∀ i, IsCompact (A i))
    (hAH : ∀ i, A i ⊆ H) (hunit : ∃ i, A i = H)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j)) :
    range (wolfeClopenTopIsometry (𝕜 := 𝕜) H hH A hA) =
      ((Submodule.span 𝕜 (range (fun i => JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)))).topologicalClosure :
        Set (JLMS.CZero 𝕜 K)) := by
  apply linearIsometry_range_eq_closedSpan _
    (wolfeClopenCoordinate (wolfeClopenTopCells H A) (wolfeClopenTopCells_isClopen H A hA))
  · exact wolfeLaminarCoordinate_dense _ _ (wolfeClopenTopCells_unit H A hunit)
      (wolfeClopenTopCells_laminar H A hlam)
  · exact wolfeClopenTopIsometry_coordinate H hH A hA hcA hAH

/-- Finite-span lower estimates on the ambient space extend to every quotient function. -/
theorem wolfeClopenTopIsometry_lower_bound {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (hH : IsClopen H) (A : ι → Set K) (hA : ∀ i, IsClopen (A i))
    (hcA : ∀ i, IsCompact (A i)) (hAH : ∀ i, A i ⊆ H) (hunit : ∃ i, A i = H)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (c : ℝ)
    (hbound : ∀ (s : Finset ι) (a : ι → 𝕜),
      c * ‖∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)‖ ≤
        ‖T (∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i))‖)
    (f : C(WolfeClopenTopQuotient H A hA, 𝕜)) :
    c * ‖f‖ ≤ ‖T (wolfeClopenTopIsometry (𝕜 := 𝕜) H hH A hA f)‖ := by
  have hf : wolfeClopenTopIsometry (𝕜 := 𝕜) H hH A hA f ∈
      (Submodule.span 𝕜 (range (fun i => JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)))).topologicalClosure :=
    (wolfeClopenTopIsometry_range H hH A hA hcA hAH hunit hlam).subset (mem_range_self f)
  have h := wolfe_lower_bound_closedSpan _ T c hbound hf
  simpa only [LinearIsometry.norm_map] using h

end Posets
