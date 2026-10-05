import Posets.MrowkaTopology
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.DerivedSet

/-! The one-point compactification of a Mrówka space has empty third
derived set. The derivative calculation itself needs no almost-disjointness;
that hypothesis supplies the Hausdorff property used in the applications. -/

noncomputable section
namespace Posets
open Set Filter Topology

theorem not_mem_derivedSet_of_isOpen_singleton {X : Type*} [TopologicalSpace X]
    {x : X} (hx : IsOpen ({x} : Set X)) (S : Set X) : x ∉ derivedSet S := by
  intro h
  obtain ⟨y, hy, hne⟩ := accPt_iff_nhds.mp h {x} (hx.mem_nhds (mem_singleton x))
  exact hne (mem_singleton_iff.mp hy.1)

theorem derivedSet_closed_singleton {X : Type*} [TopologicalSpace X]
    {x : X} (hx : IsClosed ({x} : Set X)) : derivedSet ({x} : Set X) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have he : y = x := mem_singleton_iff.mp (((isClosed_iff_derivedSet_subset _).mp hx) hy)
  subst y
  obtain ⟨z, hz, hne⟩ := accPt_iff_nhds.mp hy univ univ_mem
  exact hne (mem_singleton_iff.mp hz.2)

theorem onePointMrowka_isolated_open (𝒜 : Set (Set ℕ)) (n : ℕ) :
    IsOpen ({OnePoint.some (X := Mrowka 𝒜) (Sum.inl n)} : Set (OnePoint (Mrowka 𝒜))) := by
  simpa only [Set.image_singleton] using
    OnePoint.isOpenMap_coe ({Sum.inl n} : Set (Mrowka 𝒜)) (isolated_open 𝒜 n)

theorem onePointMrowka_secondDerived_subset (𝒜 : Set (Set ℕ)) :
    derivedSet (derivedSet (univ : Set (OnePoint (Mrowka 𝒜)))) ⊆ {OnePoint.infty} := by
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact mem_singleton _
  | coe q =>
    cases q with
    | inl n => exact (not_mem_derivedSet_of_isOpen_singleton
        (onePointMrowka_isolated_open 𝒜 n) _ hp).elim
    | inr A =>
      let U : Set (OnePoint (Mrowka 𝒜)) :=
        ((↑) : Mrowka 𝒜 → OnePoint (Mrowka 𝒜)) '' JFA.mrowkaNeighborhood 𝒜 A ∅
      have hU : IsOpen U := OnePoint.isOpenMap_coe _ (neighborhood_open 𝒜 A ∅)
      have hpU : OnePoint.some (X := Mrowka 𝒜) (Sum.inr A) ∈ U :=
        ⟨_, Or.inl rfl, rfl⟩
      obtain ⟨y, hy, hne⟩ := accPt_iff_nhds.mp hp U (hU.mem_nhds hpU)
      obtain ⟨q, hq, rfl⟩ := hy.1
      rcases hq with heq | ⟨n, _, _, heq⟩
      · exact (hne (congrArg ((↑) : Mrowka 𝒜 → OnePoint (Mrowka 𝒜)) heq)).elim
      · subst q
        exact (not_mem_derivedSet_of_isOpen_singleton
          (onePointMrowka_isolated_open 𝒜 n) _ hy.2).elim

theorem onePointMrowka_thirdDerived_empty (𝒜 : Set (Set ℕ)) :
    derivedSet (derivedSet (derivedSet (univ : Set (OnePoint (Mrowka 𝒜))))) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := derivedSet_mono _ _ (onePointMrowka_secondDerived_subset 𝒜) hp
  rw [derivedSet_closed_singleton OnePoint.isClosed_infty] at h
  exact h

end Posets
