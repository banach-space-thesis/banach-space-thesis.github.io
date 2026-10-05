import Posets.OrdinalVariableUnitColouredCores

/-! Actual sections in any selected subsequence of the variable outer
blocks uniformly escape every compact subset of the ambient interval. -/

noncomputable section
open Set Filter Topology
universe u v
namespace Posets

theorem ordinalVariableUnit_selected_escape
    {γ : Ordinal.{u}} {N : ℕ} (P : OrdinalVariableUnitParameters γ N)
    (hγ : Order.IsSuccLimit γ) (k : ℕ → ℕ) (hk : StrictMono k) {L : ℕ → Type v}
    (q : ∀ i, L i → Iio (Ordinal.omega0 ^ γ))
    (hq : ∀ i x, q i x ∈ range (P.embedding (k i))) :
    ∀ U ∈ cocompact (Iio (Ordinal.omega0 ^ γ)),
      ∀ᶠ i in cofinite, ∀ x, q i x ∈ U := by
  intro U hU
  obtain ⟨S, hS, hSU⟩ := Filter.mem_cocompact.mp hU
  have hd := P.outerBlock_escape hγ S hS
  have hd' := hk.injective.tendsto_cofinite.eventually hd
  filter_upwards [hd'] with i hi
  intro x
  apply hSU
  intro hxS
  exact Set.disjoint_left.mp hi hxS (hq i x)

end Posets
