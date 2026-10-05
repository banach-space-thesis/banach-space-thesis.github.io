import Posets.MrowkaInclusions
import Mathlib.Topology.Separation.Basic

noncomputable section
open Filter Topology
namespace Posets

/-- The natural points indexed by A converge to its family point along cofinite. -/
theorem family_tendsto (𝒜 : Set (Set ℕ)) (A : 𝒜) :
    Tendsto (fun n : A.val => (Sum.inl n.val : Mrowka 𝒜)) cofinite
      (@nhds (Mrowka 𝒜) (JFA.mrowkaTopology 𝒜) (Sum.inr A)) := by
  apply TopologicalSpace.tendsto_nhds_generateFrom_iff.mpr
  rintro U (⟨n, rfl⟩ | ⟨B, F, rfl⟩) hA
  · cases hA
  · have hAB : A = B := by
      rcases hA with hAB | ⟨_, _, _, hbad⟩
      · exact Sum.inr.inj hAB
      · cases hbad
    subst B
    have hfinite : {n : A.val | n.val ∈ F}.Finite :=
      F.finite_toSet.preimage Subtype.val_injective.injOn
    filter_upwards [hfinite.compl_mem_cofinite] with n hn
    exact Or.inr ⟨n.val, n.property, hn, rfl⟩

theorem neighborhood_empty_compact (𝒜 : Set (Set ℕ)) (A : 𝒜) :
    IsCompact (JFA.mrowkaNeighborhood 𝒜 A ∅) := by
  have h : IsCompact (insert (Sum.inr A)
      (Set.range (fun n : A.val => (Sum.inl n.val : Mrowka 𝒜))) : Set (Mrowka 𝒜)) :=
    Filter.Tendsto.isCompact_insert_range_of_cofinite (X := Mrowka 𝒜) (family_tendsto 𝒜 A)
  have heq : JFA.mrowkaNeighborhood 𝒜 A ∅ =
      insert (Sum.inr A) (Set.range (fun n : A.val => (Sum.inl n.val : Mrowka 𝒜))) := by
    ext p
    cases p <;> simp [JFA.Mrowka, JFA.mrowkaNeighborhood]
  exact heq ▸ h

instance mrowka_weaklyLocallyCompact (𝒜 : Set (Set ℕ)) : WeaklyLocallyCompactSpace (Mrowka 𝒜) where
  exists_compact_mem_nhds p := by
    cases p with
    | inl n => exact ⟨{Sum.inl n}, isCompact_singleton,
        (isolated_open 𝒜 n).mem_nhds (Set.mem_singleton _)⟩
    | inr A => exact ⟨JFA.mrowkaNeighborhood 𝒜 A ∅, neighborhood_empty_compact 𝒜 A,
        (neighborhood_open 𝒜 A ∅).mem_nhds (Or.inl rfl)⟩

/-- Almost disjointness supplies disjoint tails at distinct family points. -/
theorem mrowka_t2 (𝒜 : Set (Set ℕ)) (h𝒜 : IsAlmostDisjoint 𝒜) : T2Space (Mrowka 𝒜) where
  t2 x y hxy := by
    classical
    cases x with
    | inl n =>
      refine ⟨{Sum.inl n}, {Sum.inl n}ᶜ, isolated_open 𝒜 n,
        (isolated_clopen 𝒜 n).isClosed.isOpen_compl, Set.mem_singleton _, ?_, disjoint_compl_right⟩
      exact fun hy => hxy (Set.mem_singleton_iff.mp hy).symm
    | inr A =>
      cases y with
      | inl n =>
        refine ⟨{Sum.inl n}ᶜ, {Sum.inl n},
          (isolated_clopen 𝒜 n).isClosed.isOpen_compl, isolated_open 𝒜 n,
          ?_, Set.mem_singleton _, disjoint_compl_left⟩
        intro hbad
        cases hbad
      | inr B =>
        have hAB : A.val ≠ B.val := fun h => hxy (congrArg Sum.inr (Subtype.ext h))
        have hfin := h𝒜.2 A.val A.property B.val B.property hAB
        refine ⟨JFA.mrowkaNeighborhood 𝒜 A hfin.toFinset, JFA.mrowkaNeighborhood 𝒜 B ∅,
          neighborhood_open 𝒜 A _, neighborhood_open 𝒜 B _, Or.inl rfl, Or.inl rfl, ?_⟩
        apply Set.disjoint_left.mpr
        rintro p (rfl | ⟨n, hn, hnF, rfl⟩) hpB
        · rcases hpB with h | ⟨_, _, _, h⟩
          · exact hxy h
          · cases h
        · rcases hpB with h | ⟨m, hm, _, hnm⟩
          · cases h
          · have hnm' := Sum.inl.inj hnm
            subst m
            exact hnF (hfin.mem_toFinset.mpr ⟨hn, hm⟩)

/-- A proved instance wrapper, for use when the family hypothesis is available. -/
instance mrowka_t2_of_fact (𝒜 : Set (Set ℕ)) [h : Fact (IsAlmostDisjoint 𝒜)] :
    T2Space (Mrowka 𝒜) := mrowka_t2 𝒜 h.out

theorem mrowka_locallyCompact (𝒜 : Set (Set ℕ)) (h𝒜 : IsAlmostDisjoint 𝒜) :
    LocallyCompactSpace (Mrowka 𝒜) := by
  letI := mrowka_t2 𝒜 h𝒜
  infer_instance

end Posets
