import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

open Filter Topology
namespace ThesisCommon

/-- If a continuous image converges to a point outside the map's range in a
Hausdorff space, the original net eventually avoids each compact set. -/
theorem tendsto_cocompact_of_tendsto_outside_range {X Y I : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (g : I → X) (l : Filter I) (y : Y)
    (hy : y ∉ Set.range f) (hg : Tendsto (f ∘ g) l (𝓝 y)) :
    Tendsto g l (cocompact X) := by
  apply hasBasis_cocompact.tendsto_right_iff.mpr
  intro K hK
  have hnot : y ∈ (f '' K)ᶜ := fun h => hy (Set.image_subset_range f K h)
  have h := hg.eventually ((hK.image hf).isClosed.isOpen_compl.mem_nhds hnot)
  filter_upwards [h] with i hi
  exact fun hgi => hi ⟨g i, hgi, rfl⟩

end ThesisCommon
