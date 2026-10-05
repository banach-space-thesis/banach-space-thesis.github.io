import Posets.WolfeLaminarEmbeddingClopenTop
import JLMS.CZeroSumSynthesis

/-! An isometric sum of embeddings supported on pairwise disjoint cells.
The actual c₀ sum is sent to the norm-convergent sum of its coordinates. -/
noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

local instance wolfeDisjointSumGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance wolfeDisjointSumSpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem wolfe_disjoint_finite_sum_bound
    (H : I → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (J : ∀ i, E i →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ H i)
    (f : ∀ i, E i) (s : Finset I) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ M) : ‖∑ i ∈ s, J i (f i)‖ ≤ M := by
  classical
  apply (BoundedContinuousFunction.norm_le hM).mpr
  intro x
  change ‖JLMS.evaluation x (∑ i ∈ s, J i (f i))‖ ≤ M
  rw [map_sum]
  by_cases hx : ∃ i ∈ s, x ∈ H i
  · obtain ⟨i, hi, hxi⟩ := hx
    rw [Finset.sum_eq_single i]
    · exact (JLMS.norm_CZero_apply_le (J i (f i)) x).trans (by simpa using hf i hi)
    · intro j _ hji
      by_contra h
      exact Set.disjoint_left.mp (hH hji) (hsupp j (f j) h) hxi
    · exact fun h => (h hi).elim
  · have hz : ∀ i ∈ s, JLMS.evaluation x (J i (f i)) = 0 := by
      intro i hi
      by_contra h
      exact hx ⟨i, hi, hsupp i (f i) h⟩
    rw [Finset.sum_eq_zero hz, norm_zero]
    exact hM

def wolfeDisjointSynthesis
    (H : I → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (J : ∀ i, E i →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ H i) :
    JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZero 𝕜 K :=
  JLMS.cZeroSumSynthesis (fun i => (J i).toContinuousLinearMap)
    (wolfe_disjoint_finite_sum_bound H hH J hsupp)

theorem wolfeDisjointSynthesis_apply_mem
    (H : I → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (J : ∀ i, E i →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ H i)
    (f : JLMS.CZeroSum 𝕜 E) {i : I} {x : K} (hx : x ∈ H i) :
    wolfeDisjointSynthesis H hH J hsupp f x = J i (f i) x := by
  classical
  have heval := (JLMS.evaluation x).hasSum
    (JLMS.hasSum_cZeroSumSynthesis (fun i => (J i).toContinuousLinearMap)
      (wolfe_disjoint_finite_sum_bound H hH J hsupp) f)
  change HasSum (fun j => J j (f j) x) (wolfeDisjointSynthesis H hH J hsupp f x) at heval
  rw [← heval.tsum_eq, tsum_eq_single i]
  intro j hji
  by_contra h
  exact Set.disjoint_left.mp (hH hji) (hsupp j (f j) h) hx

theorem wolfeDisjointSynthesis_norm
    (H : I → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (J : ∀ i, E i →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ H i)
    (f : JLMS.CZeroSum 𝕜 E) : ‖wolfeDisjointSynthesis H hH J hsupp f‖ = ‖f‖ := by
  apply le_antisymm
  · exact JLMS.norm_cZeroSum_coordinates_tsum_le (fun i => (J i).toContinuousLinearMap)
      (wolfe_disjoint_finite_sum_bound H hH J hsupp) f
  · apply JLMS.CZeroSum.norm_le (norm_nonneg _)
    intro i
    rw [← (J i).norm_map]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro x
    change ‖J i (f i) x‖ ≤ _
    by_cases hx : x ∈ H i
    · rw [← wolfeDisjointSynthesis_apply_mem H hH J hsupp f hx]
      exact JLMS.norm_CZero_apply_le _ x
    · have hz : J i (f i) x = 0 := by
        by_contra h
        exact hx (hsupp i (f i) h)
      rw [hz, norm_zero]
      exact norm_nonneg _

def wolfeDisjointSumIsometry
    (H : I → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (J : ∀ i, E i →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ H i) :
    JLMS.CZeroSum 𝕜 E →ₗᵢ[𝕜] JLMS.CZero 𝕜 K where
  toLinearMap := (wolfeDisjointSynthesis H hH J hsupp).toLinearMap
  norm_map' := wolfeDisjointSynthesis_norm H hH J hsupp

end Posets

