import Posets.OrdinalRegularOmegaColouredCores

/-! Any sequence of points in the selected outer blocks escapes every
compact set. This applies uniformly to all points of each section. -/

noncomputable section
open Set Filter Topology
universe u v
namespace Posets

theorem ordinalRegularOmega_selected_escape
    (c : Cardinal.{u}) (hu : Cardinal.aleph0 < c) (N : ℕ)
    (k : ℕ → ℕ) (hk : StrictMono k) {L : ℕ → Type v}
    (q : ∀ i, L i → Iio (c.ord ^ Ordinal.omega0))
    (hq : ∀ i x, q i x ∈ range (ordinalRegularOmegaSourceEmbedding c hu N (k i))) :
    ∀ U ∈ cocompact (Iio (c.ord ^ Ordinal.omega0)),
      ∀ᶠ i in cofinite, ∀ x, q i x ∈ U := by
  intro U hU
  obtain ⟨S, hS, hSU⟩ := Filter.mem_cocompact.mp hU
  have hd := ordinalRegularOmegaOuterFamily_escape c hu.le
    (ordinalRegularOmegaOuterHeight N) (ordinalRegularOmegaOuterHeight_strictMono N) S hS
  have hd' := hk.injective.tendsto_cofinite.eventually hd
  filter_upwards [hd'] with i hi
  intro x
  apply hSU
  intro hxS
  exact Set.disjoint_left.mp hi hxS (hq i x)

end Posets
