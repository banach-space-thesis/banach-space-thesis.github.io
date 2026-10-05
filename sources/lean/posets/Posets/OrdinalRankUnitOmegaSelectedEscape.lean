import Posets.OrdinalRankUnitOmegaColouredCores

/-! Any sequence of points in the selected outer blocks escapes every
compact set. This applies uniformly to all points of each section. -/

noncomputable section
open Set Filter Topology
universe u v
namespace Posets

theorem ordinalRankUnitOmega_selected_escape
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) (N : ℕ)
    (k : ℕ → ℕ) (hk : StrictMono k) {L : ℕ → Type v}
    (q : ∀ i, L i → Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))
    (hq : ∀ i x, q i x ∈ range (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (k i))) :
    ∀ U ∈ cocompact (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)),
      ∀ᶠ i in cofinite, ∀ x, q i x ∈ U := by
  intro U hU
  obtain ⟨S, hS, hSU⟩ := Filter.mem_cocompact.mp hU
  have hd := ordinalRankUnitOmegaOuterFamily_escape ρ hρ
    (ordinalRankUnitOmegaOuterHeight N) (ordinalRankUnitOmegaOuterHeight_strictMono N) S hS
  have hd' := hk.injective.tendsto_cofinite.eventually hd
  filter_upwards [hd'] with i hi
  intro x
  apply hSU
  intro hxS
  exact Set.disjoint_left.mp hi hxS (hq i x)

end Posets


