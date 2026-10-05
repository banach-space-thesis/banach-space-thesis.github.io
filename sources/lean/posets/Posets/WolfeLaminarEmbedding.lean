import Posets.WolfeLaminarEmbeddingAlgebra
import Posets.WolfeLaminarEmbeddingRange
import Posets.WolfeLaminarSpan

/-! The closed span of a unital laminar clopen family is exactly an
isometric copy of the continuous-function space of its membership quotient. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K ι : Type*} [RCLike 𝕜] [TopologicalSpace K] [CompactSpace K]
variable (A : ι → Set K) (hA : ∀ i, IsClopen (A i))

theorem wolfeLaminarCoordinate_dense
    (hunit : ∃ i, A i = univ)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j)) :
    Dense (Submodule.span 𝕜 (range (wolfeClopenCoordinate (𝕜 := 𝕜) A hA)) :
      Set C(WolfeClopenQuotient A hA, 𝕜)) := by
  apply wolfe_generatorSpan_dense
  · obtain ⟨i, hi⟩ := hunit
    exact ⟨i, wolfeClopenCoordinate_one A hA hi⟩
  · exact wolfeClopenCoordinate_star A hA
  · exact wolfeClopenCoordinate_mul_mem_span A hA hlam
  · exact wolfeClopenCoordinate_separates A hA

theorem wolfeLaminarEmbedding_range (hcA : ∀ i, IsCompact (A i))
    (hunit : ∃ i, A i = univ)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j)) :
    range (wolfeClopenCZeroIsometry (𝕜 := 𝕜) A hA) =
      ((Submodule.span 𝕜 (range (fun i => JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)))).topologicalClosure :
        Set (JLMS.CZero 𝕜 K)) := by
  apply linearIsometry_range_eq_closedSpan _ (wolfeClopenCoordinate A hA)
  · exact wolfeLaminarCoordinate_dense A hA hunit hlam
  · exact wolfeClopenCZeroIsometry_coordinate A hA

theorem wolfeLaminarEmbedding_lower_bound {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (hcA : ∀ i, IsCompact (A i)) (hunit : ∃ i, A i = univ)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (c : ℝ)
    (hbound : ∀ (s : Finset ι) (a : ι → 𝕜),
      c * ‖∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)‖ ≤
        ‖T (∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i))‖)
    (f : C(WolfeClopenQuotient A hA, 𝕜)) :
    c * ‖f‖ ≤ ‖T (wolfeClopenCZeroIsometry (𝕜 := 𝕜) A hA f)‖ := by
  have hf : wolfeClopenCZeroIsometry (𝕜 := 𝕜) A hA f ∈
      (Submodule.span 𝕜 (range (fun i => JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)))).topologicalClosure := by
    exact (wolfeLaminarEmbedding_range (𝕜 := 𝕜) A hA hcA hunit hlam).subset (mem_range_self f)
  have h := wolfe_lower_bound_closedSpan _ T c hbound hf
  simpa only [LinearIsometry.norm_map] using h

end Posets


