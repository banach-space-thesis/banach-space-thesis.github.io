import JLMS.NeighborhoodProjection
import Mathlib.Topology.Separation.Profinite

/-!
# Section 4: topology of scattered locally compact Hausdorff spaces

The argument follows the paper: isolated points rule out nonsingleton
connected subsets; mathlib's locally compact Hausdorff theorem then gives
a clopen base. Refinement inside a compact neighborhood gives a compact
clopen base. Finally finitely many distinct points are separated simultaneously.
-/

noncomputable section

open Set Topology

namespace JLMS

variable {K : Type*} [TopologicalSpace K]

/-- A preconnected subset of a scattered T₁ space has at most one point. -/
theorem scattered_preconnected_subsingleton [T1Space K] (hK : IsScattered K)
    {s : Set K} (hs : IsPreconnected s) : s.Subsingleton := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact Set.subsingleton_empty
  obtain ⟨x, hxs, U, hU, hinter⟩ := hK s hne
  have hxU : x ∈ U := by
    have : x ∈ s ∩ U := by rw [hinter]; exact Set.mem_singleton x
    exact this.2
  have hsub : s ⊆ {x} := by
    intro y hys
    by_contra hy
    have hcover : s ⊆ U ∪ ({x} : Set K)ᶜ := by
      intro z _
      by_cases hz : z = x
      · exact Or.inl (hz ▸ hxU)
      · exact Or.inr (by simpa using hz)
    obtain ⟨z, hzs, hzU, hznot⟩ := hs U ({x} : Set K)ᶜ hU
      isClosed_singleton.isOpen_compl hcover ⟨x, hxs, hxU⟩ ⟨y, hys, hy⟩
    have hz : z = x := Set.mem_singleton_iff.mp (hinter ▸ ⟨hzs, hzU⟩)
    exact hznot (by simp [hz])
  exact Set.subsingleton_singleton.anti hsub

theorem scattered_totallyDisconnected [T1Space K] (hK : IsScattered K) :
    TotallyDisconnectedSpace K :=
  ⟨fun _ _ hs => scattered_preconnected_subsingleton hK hs⟩

/-- Every neighborhood contains a compact clopen neighborhood of its point. -/
theorem exists_compact_clopen_subset [LocallyCompactSpace K] [T2Space K]
    (hK : IsScattered K) {x : K} {O : Set K} (hO : IsOpen O) (hx : x ∈ O) :
    ∃ U : Set K, IsClopen U ∧ IsCompact U ∧ x ∈ U ∧ U ⊆ O := by
  letI : TotallyDisconnectedSpace K := scattered_totallyDisconnected hK
  obtain ⟨C, hC, hxC, hCO⟩ := exists_compact_subset hO hx
  obtain ⟨U, hU, hxU, hUC⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.exists_subset_of_mem_open hxC isOpen_interior
  exact ⟨U, hU, hC.of_isClosed_subset hU.isClosed (hUC.trans interior_subset),
    hxU, hUC.trans (interior_subset.trans hCO)⟩

/-- Finite distinct points admit a pairwise disjoint compact clopen
neighborhood family, the input needed by the proved projection module. -/
theorem exists_neighborhoodFamily [LocallyCompactSpace K] [T2Space K]
    (hK : IsScattered K) {ι : Type*} [Fintype ι] (p : ι → K)
    (hp : Function.Injective p) : Nonempty (NeighborhoodFamily p) := by
  classical
  have hsep : ∀ i j : ι, ∃ A B : Set K,
      IsOpen A ∧ IsOpen B ∧ p i ∈ A ∧ p j ∈ B ∧ (i ≠ j → Disjoint A B) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨univ, univ, isOpen_univ, isOpen_univ, mem_univ _, mem_univ _,
        fun h => False.elim (h hij)⟩
    · obtain ⟨A, B, hA, hB, hi, hj, hd⟩ := t2_separation (hp.ne hij)
      exact ⟨A, B, hA, hB, hi, hj, fun _ => hd⟩
  choose A B hA hB hi hj hd using hsep
  let O : ι → Set K := fun i => ⋂ j, A i j ∩ B j i
  have hO (i : ι) : IsOpen (O i) :=
    isOpen_iInter_of_finite fun j => (hA i j).inter (hB j i)
  have hpO (i : ι) : p i ∈ O i := mem_iInter.mpr fun j => ⟨hi i j, hj j i⟩
  choose U hUclopen hUcompact hpU hUO using
    fun i => exists_compact_clopen_subset hK (hO i) (hpO i)
  refine ⟨⟨U, hUclopen, hUcompact, hpU, ?_⟩⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hxAi : x ∈ A i j := (mem_iInter.mp (hUO i hxi) j).1
  have hxBj : x ∈ B i j := (mem_iInter.mp (hUO j hxj) i).2
  exact Set.disjoint_left.mp (hd i j hij) hxAi hxBj

/-- Shrink a finite neighborhood family inside an additional open set. This
is the refinement used to avoid earlier neighborhoods and finite tail atoms. -/
theorem exists_neighborhoodFamily_shrink [LocallyCompactSpace K] [T2Space K]
    (hK : IsScattered K) {ι : Type*} [Fintype ι] {p : ι → K}
    (U : NeighborhoodFamily p) {O : Set K} (hO : IsOpen O) (hpO : ∀ i, p i ∈ O) :
    ∃ V : NeighborhoodFamily p, ∀ i, V.sets i ⊆ U.sets i ∩ O := by
  classical
  choose V hclopen hcompact hcontains hsub using fun i =>
    exists_compact_clopen_subset hK ((U.clopen i).isOpen.inter hO)
      (show p i ∈ U.sets i ∩ O from ⟨U.contains i, hpO i⟩)
  refine ⟨⟨V, hclopen, hcompact, hcontains, ?_⟩, hsub⟩
  intro i j hij
  exact (U.disjoint hij).mono (fun x hx => (hsub i hx).1) (fun x hx => (hsub j hx).1)

/-- Every compact set lies in a compact clopen set. A finite subcover of the
compact clopen neighborhood base gives the cutoff sets used in Riesz representation. -/
theorem exists_compact_clopen_superset [LocallyCompactSpace K] [T2Space K]
    (hK : IsScattered K) {C : Set K} (hC : IsCompact C) :
    ∃ U : Set K, IsClopen U ∧ IsCompact U ∧ C ⊆ U := by
  classical
  choose U hclopen hcompact hcontains hsub using fun x : C =>
    exists_compact_clopen_subset hK isOpen_univ (mem_univ x.val)
  have hcover : C ⊆ ⋃ x : C, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hcontains ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U (fun x => (hclopen x).isOpen) hcover
  exact ⟨⋃ x ∈ t, U x, isClopen_biUnion_finset (fun x _ => hclopen x),
    t.isCompact_biUnion (fun x _ => hcompact x), ht⟩

end JLMS
