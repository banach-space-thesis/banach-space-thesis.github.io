import Posets.MrowkaLimits

noncomputable section
open Filter Topology
namespace Posets

/-- A function on the concrete Mrówka space is continuous exactly when its
values along each family member converge to the value at the corresponding point. -/
theorem mrowka_continuous_iff {𝒜 : Set (Set ℕ)} {Y : Type*} [TopologicalSpace Y]
    (g : Mrowka 𝒜 → Y) :
    Continuous g ↔ ∀ A : 𝒜, Tendsto (fun n => g (Sum.inl n)) (Along A.val) (𝓝 (g (Sum.inr A))) := by
  constructor
  · intro hg A
    exact hg.continuousAt.tendsto.comp (family_tendsto_along 𝒜 A)
  · intro h
    apply continuous_iff_continuousAt.mpr
    intro p
    apply tendsto_def.mpr
    intro V hV
    cases p with
    | inl n =>
      apply Filter.mem_of_superset ((isolated_open 𝒜 n).mem_nhds (Set.mem_singleton _))
      rintro q rfl
      have hv : g (Sum.inl n) ∈ V := mem_of_mem_nhds hV
      exact hv
    | inr A =>
      have hgood := mem_inf_principal.mp ((h A).eventually hV)
      have hfin := eventually_cofinite.mp hgood
      apply Filter.mem_of_superset
        ((neighborhood_open 𝒜 A hfin.toFinset).mem_nhds (Or.inl rfl))
      rintro q (rfl | ⟨n, hn, hnF, rfl⟩)
      · have hv : g (Sum.inr A) ∈ V := mem_of_mem_nhds hV
        exact hv
      · have hn' : n ∈ A.val → g (Sum.inl n) ∈ V := by
          simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hnF
        exact hn' hn

end Posets
