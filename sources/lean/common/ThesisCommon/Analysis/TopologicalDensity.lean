import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! Cardinal density, defined by actual dense subsets.  The minimum is attained
because cardinals are well ordered.  No separability or countability hypothesis
is imposed. -/
noncomputable section
open Set
namespace ThesisCommon
universe u

/-- The least cardinality of a dense subset, including the empty-space case. -/
def topologicalDensity (X : Type u) [TopologicalSpace X] : Cardinal.{u} :=
  sInf {c | ∃ s : Set X, Dense s ∧ Cardinal.mk s = c}

theorem exists_dense_card_eq_topologicalDensity (X : Type u) [TopologicalSpace X] :
    ∃ s : Set X, Dense s ∧ Cardinal.mk s = topologicalDensity X := by
  change sInf {c | ∃ s : Set X, Dense s ∧ Cardinal.mk s = c} ∈
    {c | ∃ s : Set X, Dense s ∧ Cardinal.mk s = c}
  apply csInf_mem
  exact ⟨Cardinal.mk (univ : Set X), univ, dense_univ, rfl⟩

theorem topologicalDensity_le_card_of_dense {X : Type u} [TopologicalSpace X]
    {s : Set X} (hs : Dense s) : topologicalDensity X ≤ Cardinal.mk s :=
  csInf_le' ⟨s, hs, rfl⟩

theorem topologicalDensity_le_of_continuous_surjective {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (hfs : Function.Surjective f) :
    topologicalDensity Y ≤ topologicalDensity X := by
  obtain ⟨s, hs, hcard⟩ := exists_dense_card_eq_topologicalDensity X
  calc
    topologicalDensity Y ≤ Cardinal.mk (f '' s) :=
      topologicalDensity_le_card_of_dense (hfs.denseRange.dense_image hf hs)
    _ ≤ Cardinal.mk s := Cardinal.mk_image_le
    _ = topologicalDensity X := hcard

theorem topologicalDensity_eq_of_homeomorph {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    topologicalDensity X = topologicalDensity Y :=
  le_antisymm
    (topologicalDensity_le_of_continuous_surjective e.symm.continuous e.symm.surjective)
    (topologicalDensity_le_of_continuous_surjective e.continuous e.surjective)

end ThesisCommon
