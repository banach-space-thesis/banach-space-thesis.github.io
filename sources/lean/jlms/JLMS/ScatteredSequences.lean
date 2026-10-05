import JLMS.ScatteredTopology
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Sequential compactness of compact scattered spaces

The cluster set of a sequence is nonempty by compactness. An isolated point
of that cluster set admits a compact clopen neighborhood containing no other
cluster point. The subsequence in this neighborhood therefore converges.
This supplies the point sequences for the complemented-copy construction.
-/

noncomputable section

open Set Filter Topology

namespace JLMS

variable {K : Type*} [TopologicalSpace K]

/-- A compact scattered Hausdorff space is sequentially compact, without
first-countability or metrizability assumptions. -/
theorem scattered_compact_subsequence [CompactSpace K] [T2Space K]
    (hK : IsScattered K) (u : ℕ → K) :
    ∃ x : K, ∃ s : ℕ → ℕ, StrictMono s ∧ Tendsto (u ∘ s) atTop (𝓝 x) := by
  let L : Set K := {x | MapClusterPt x atTop u}
  have hL : L.Nonempty := exists_clusterPt_of_compactSpace (map u atTop)
  obtain ⟨x, hx, U, hU, hLU⟩ := hK L hL
  have hxU : x ∈ U := by
    have hm : x ∈ L ∩ U := by rw [hLU]; exact mem_singleton x
    exact hm.2
  obtain ⟨W, hW, hcW, hxW, hWU⟩ := exists_compact_clopen_subset hK hU hxU
  obtain ⟨s, hs, hus⟩ := extraction_of_frequently_atTop
    (hx.frequently (hW.isOpen.mem_nhds hxW))
  refine ⟨x, s, hs, hcW.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall hus) ?_⟩
  intro y hy hcluster
  have hyL : y ∈ L := hcluster.of_comp hs.tendsto_atTop
  exact mem_singleton_iff.mp (hLU ▸ (show y ∈ L ∩ U from ⟨hyL, hWU hy⟩))

theorem scattered_seqCompactSpace [CompactSpace K] [T2Space K]
    (hK : IsScattered K) : SeqCompactSpace K := by
  constructor
  intro u hu
  obtain ⟨x, s, hs, ht⟩ := scattered_compact_subsequence hK u
  exact ⟨x, mem_univ x, s, hs, ht⟩

/-- Adding the point at infinity preserves scatteredness. -/
theorem scattered_onePoint (hK : IsScattered K) : IsScattered (OnePoint K) := by
  intro S hS
  let A : Set K := OnePoint.some ⁻¹' S
  by_cases hA : A.Nonempty
  · obtain ⟨x, hx, U, hU, hAU⟩ := hK A hA
    have hxU : x ∈ U := by
      have hm : x ∈ A ∩ U := by rw [hAU]; exact mem_singleton x
      exact hm.2
    refine ⟨(x : OnePoint K), hx, OnePoint.some '' U, OnePoint.isOpenMap_coe U hU, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, y, hy, rfl⟩
      have he : y = x := mem_singleton_iff.mp (hAU ▸ (show y ∈ A ∩ U from ⟨hz, hy⟩))
      simpa [he]
    · rintro rfl
      exact ⟨hx, x, hxU, rfl⟩
  · have hsub : S ⊆ {OnePoint.infty} := by
      intro z hz
      induction z using OnePoint.rec with
      | infty => exact mem_singleton _
      | coe x => exact False.elim (hA ⟨x, hz⟩)
    obtain ⟨z, hz⟩ := hS
    have he : z = OnePoint.infty := hsub hz
    refine ⟨OnePoint.infty, he ▸ hz, univ, isOpen_univ, ?_⟩
    rw [inter_univ]
    exact Subset.antisymm hsub (singleton_subset_iff.mpr (he ▸ hz))

/-- Every infinite scattered locally compact Hausdorff K has a sequence
of distinct points converging in its one-point compactification. -/
theorem exists_injective_onePoint_convergent [LocallyCompactSpace K] [T2Space K]
    [Infinite K] (hK : IsScattered K) :
    ∃ p : ℕ → K, Function.Injective p ∧ ∃ x : OnePoint K,
      Tendsto (fun n => (p n : OnePoint K)) atTop (𝓝 x) := by
  let j : ℕ ↪ K := Infinite.natEmbedding K
  obtain ⟨x, s, hs, ht⟩ := scattered_compact_subsequence (scattered_onePoint hK)
    (fun n => (j n : OnePoint K))
  exact ⟨j ∘ s, j.injective.comp hs.injective, x, ht⟩

end JLMS
