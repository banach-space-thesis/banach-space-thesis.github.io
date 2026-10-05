import ThesisCommon.Analysis.OrdinalDerived
import Mathlib.Data.Set.Lattice.Image

/-! Transfinite derivatives commute with closed topological embeddings. This
allows the increasing ordinal model of a compact set to carry the original
characteristic rank without changing the ambient-space convention. -/
noncomputable section
open Set Filter Topology Order
universe u v w
namespace ThesisCommon
variable {K : Type v} {L : Type w} [TopologicalSpace K] [TopologicalSpace L]

theorem derivedSet_image_closedEmbedding {f : K → L} (hf : IsClosedEmbedding f)
    (A : Set K) : derivedSet (f '' A) = f '' derivedSet A := by
  apply Subset.antisymm
  · intro z hz
    have hzrange : z ∈ range f := hf.isClosed_range.closure_subset
      ((closure_mono (image_subset_range f A)) (derivedSet_subset_closure _ hz))
    obtain ⟨x, rfl⟩ := hzrange
    refine ⟨x, ?_, rfl⟩
    rw [mem_derivedSet, accPt_iff_nhds]
    intro U hU
    rw [hf.isEmbedding.isInducing.nhds_eq_comap] at hU
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
    obtain ⟨z, ⟨hzV, hzA⟩, hzx⟩ := (accPt_iff_nhds.mp hz) V hV
    obtain ⟨a, ha, rfl⟩ := hzA
    refine ⟨a, ⟨hVU hzV, ha⟩, ?_⟩
    intro hax
    exact hzx (congrArg f hax)
  · exact hf.continuous.image_derivedSet hf.injective

theorem ordinalDerived_image_closedEmbedding {f : K → L} (hf : IsClosedEmbedding f)
    (A : Set K) (α : Ordinal.{u}) :
    ordinalDerived (f '' A) α = f '' ordinalDerived A α := by
  induction α using Ordinal.limitRecOn with
  | zero => simp
  | succ α ih =>
      rw [ordinalDerived_succ, ordinalDerived_succ, ih, derivedSet_image_closedEmbedding hf]
  | limit α hα ih =>
      rw [ordinalDerived_limit _ hα, ordinalDerived_limit _ hα]
      rw [hf.injective.injOn.image_biInter_eq ⟨0, hα.bot_lt⟩]
      exact iInter_congr fun β => iInter_congr fun hβ => ih β hβ

end ThesisCommon
