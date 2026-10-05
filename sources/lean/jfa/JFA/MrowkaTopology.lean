import JFA.Definitions
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.DiscreteSubset

/-! The actual topology used by the Section 4 statements. Co-finite tails form
a neighborhood basis at each family point. Each tail is compact, the space is
locally compact, and almost-disjointness makes it Hausdorff. -/

noncomputable section
open TopologicalSpace Topology Filter Set
namespace JFA
-- Keep the type synonym opaque elsewhere so its topology is not confused with
-- a coproduct topology. The constructor calculations here use local unfolding.
set_option allowUnsafeReducibility true in
attribute [local reducible] Mrowka
variable {𝒜 : Set (Set ℕ)}
local instance : TopologicalSpace (Mrowka 𝒜) := mrowkaTopology 𝒜

@[simp] theorem mrowka_inl_mem (A : 𝒜) (G : Finset ℕ) (n : ℕ) :
    Sum.inl n ∈ mrowkaNeighborhood 𝒜 A G ↔ n ∈ (A : Set ℕ) ∧ n ∉ G := by
  simp [mrowkaNeighborhood]

@[simp] theorem mrowka_inr_mem (A B : 𝒜) (G : Finset ℕ) :
    Sum.inr B ∈ mrowkaNeighborhood 𝒜 A G ↔ B = A := by
  simp [mrowkaNeighborhood]

theorem mrowka_isOpen_singleton (n : ℕ) : IsOpen ({Sum.inl n} : Set (Mrowka 𝒜)) :=
  isOpen_generateFrom_of_mem (Or.inl ⟨n, rfl⟩)

theorem mrowka_isOpen_neighborhood (A : 𝒜) (G : Finset ℕ) :
    IsOpen (mrowkaNeighborhood 𝒜 A G) :=
  isOpen_generateFrom_of_mem (Or.inr ⟨A, G, rfl⟩)

theorem mrowka_neighborhood_inter (A : 𝒜) (G H : Finset ℕ) :
    mrowkaNeighborhood 𝒜 A (G ∪ H) =
      mrowkaNeighborhood 𝒜 A G ∩ mrowkaNeighborhood 𝒜 A H := by
  ext p
  cases p with
  | inl n => simp only [mrowka_inl_mem, mem_inter_iff, Finset.mem_union, not_or]; tauto
  | inr B => simp only [mrowka_inr_mem, mem_inter_iff, and_self]

theorem mrowka_open_contains_tail {U : Set (Mrowka 𝒜)} (hU : IsOpen U)
    (A : 𝒜) (hA : Sum.inr A ∈ U) :
    ∃ G : Finset ℕ, mrowkaNeighborhood 𝒜 A G ⊆ U := by
  change GenerateOpen
    ({V | ∃ n : ℕ, V = {Sum.inl n}} ∪
      {V | ∃ B : 𝒜, ∃ G : Finset ℕ, V = mrowkaNeighborhood 𝒜 B G}) U at hU
  induction hU with
  | basic V hV =>
    rcases hV with ⟨n, rfl⟩ | ⟨B, G, rfl⟩
    · simp only [mem_singleton_iff] at hA
      cases hA
    · have hAB : A = B := mrowka_inr_mem B A G |>.mp hA
      subst B
      exact ⟨G, Subset.rfl⟩
  | univ => exact ⟨∅, subset_univ _⟩
  | inter U V _ _ hU hV =>
    obtain ⟨G, hG⟩ := hU hA.1
    obtain ⟨H, hH⟩ := hV hA.2
    refine ⟨G ∪ H, ?_⟩
    rw [mrowka_neighborhood_inter]
    exact inter_subset_inter hG hH
  | sUnion S _ hS =>
    obtain ⟨V, hVS, hAV⟩ := hA
    obtain ⟨G, hG⟩ := hS V hVS hAV
    exact ⟨G, hG.trans (subset_sUnion_of_mem hVS)⟩

theorem mrowka_tail_mem_nhds (A : 𝒜) (G : Finset ℕ) :
    mrowkaNeighborhood 𝒜 A G ∈ 𝓝 (Sum.inr A) :=
  (mrowka_isOpen_neighborhood A G).mem_nhds (by simp)

theorem mrowka_isCompact_neighborhood (A : 𝒜) (G : Finset ℕ) :
    IsCompact (mrowkaNeighborhood 𝒜 A G) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hcover
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hcover (by simp : Sum.inr A ∈ mrowkaNeighborhood 𝒜 A G))
  obtain ⟨H, hH⟩ := mrowka_open_contains_tail (hU i₀) A hi₀
  let D : Set (Mrowka 𝒜) := mrowkaNeighborhood 𝒜 A G \ U i₀
  have hD : D.Finite := (H.finite_toSet.image (Sum.inl : ℕ → Mrowka 𝒜)).subset (by
    intro p hp
    cases p with
    | inr B =>
      have hBA := (mrowka_inr_mem A B G).mp hp.1
      subst B
      exact False.elim (hp.2 hi₀)
    | inl n =>
      have hnA := (mrowka_inl_mem A G n).mp hp.1
      have hnH : n ∈ H := by
        by_contra hnH
        exact hp.2 (hH ((mrowka_inl_mem A H n).mpr ⟨hnA.1, hnH⟩))
      exact ⟨n, hnH, rfl⟩)
  obtain ⟨t, ht⟩ := hD.isCompact.elim_finite_subcover U hU (fun p hp => hcover hp.1)
  refine ⟨insert i₀ t, ?_⟩
  intro p hp
  by_cases hp₀ : p ∈ U i₀
  · exact mem_iUnion₂.mpr ⟨i₀, Finset.mem_insert_self _ _, hp₀⟩
  · obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (ht ⟨hp, hp₀⟩)
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hpi⟩

theorem mrowka_locallyCompactSpace : LocallyCompactSpace (Mrowka 𝒜) := by
  constructor
  intro p V hV
  obtain ⟨U, hUV, hU, hpU⟩ := mem_nhds_iff.mp hV
  cases p with
  | inl n =>
    exact ⟨{Sum.inl n}, (mrowka_isOpen_singleton n).mem_nhds (mem_singleton _),
      (singleton_subset_iff.mpr hpU).trans hUV, isCompact_singleton⟩
  | inr A =>
    obtain ⟨G, hG⟩ := mrowka_open_contains_tail hU A hpU
    exact ⟨mrowkaNeighborhood 𝒜 A G, mrowka_tail_mem_nhds A G,
      hG.trans hUV, mrowka_isCompact_neighborhood A G⟩

theorem mrowka_t2Space (h𝒜 : IsAlmostDisjoint 𝒜) : T2Space (Mrowka 𝒜) := by
  classical
  constructor
  intro p q hpq
  cases p with
  | inl n =>
    cases q with
    | inl m =>
      refine ⟨{Sum.inl n}, {Sum.inl m}, mrowka_isOpen_singleton n, mrowka_isOpen_singleton m,
        mem_singleton _, mem_singleton _, ?_⟩
      exact disjoint_singleton.mpr hpq
    | inr A =>
      refine ⟨{Sum.inl n}, mrowkaNeighborhood 𝒜 A {n}, mrowka_isOpen_singleton n,
        mrowka_isOpen_neighborhood A {n}, mem_singleton _, by simp, ?_⟩
      rw [disjoint_singleton_left]
      simp
  | inr A =>
    cases q with
    | inl n =>
      refine ⟨mrowkaNeighborhood 𝒜 A {n}, {Sum.inl n}, mrowka_isOpen_neighborhood A {n},
        mrowka_isOpen_singleton n, by simp, mem_singleton _, ?_⟩
      rw [disjoint_singleton_right]
      simp
    | inr B =>
      have hAB : (A : Set ℕ) ≠ B := fun h => hpq (congrArg Sum.inr (Subtype.ext h))
      have hfin := h𝒜.2 A A.property B B.property hAB
      let G := hfin.toFinset
      refine ⟨mrowkaNeighborhood 𝒜 A G, mrowkaNeighborhood 𝒜 B ∅,
        mrowka_isOpen_neighborhood A G, mrowka_isOpen_neighborhood B ∅, by simp, by simp, ?_⟩
      apply disjoint_left.mpr
      intro z hzA hzB
      cases z with
      | inr C =>
        have hCA := (mrowka_inr_mem A C G).mp hzA
        have hCB := (mrowka_inr_mem B C ∅).mp hzB
        exact hAB (congrArg Subtype.val (hCA.symm.trans hCB))
      | inl n =>
        have hnA := (mrowka_inl_mem A G n).mp hzA
        have hnB := (mrowka_inl_mem B ∅ n).mp hzB
        exact hnA.2 (hfin.mem_toFinset.mpr ⟨hnA.1, hnB.1⟩)

theorem mrowka_inl_denseRange (h𝒜 : IsAlmostDisjoint 𝒜) :
    DenseRange (Sum.inl : ℕ → Mrowka 𝒜) := by
  intro p
  apply mem_closure_iff.mpr
  intro U hU hpU
  cases p with
  | inl n => exact ⟨Sum.inl n, hpU, ⟨n, rfl⟩⟩
  | inr A =>
    obtain ⟨G, hG⟩ := mrowka_open_contains_tail hU A hpU
    obtain ⟨n, hnA, hnG⟩ := ((h𝒜.1 A A.property).diff G.finite_toSet).nonempty
    exact ⟨Sum.inl n, hG ((mrowka_inl_mem A G n).mpr ⟨hnA, hnG⟩), ⟨n, rfl⟩⟩

theorem mrowka_separableSpace (h𝒜 : IsAlmostDisjoint 𝒜) :
    SeparableSpace (Mrowka 𝒜) :=
  SeparableSpace.of_denseRange _ (mrowka_inl_denseRange h𝒜)

/-- The closed set of family points, with its actual subspace topology. -/
def mrowkaRemainder (𝒜 : Set (Set ℕ)) : Set (Mrowka 𝒜) :=
  Set.range (Sum.inr : 𝒜 → Mrowka 𝒜)

theorem mrowka_remainder_isClosed : IsClosed (mrowkaRemainder 𝒜) := by
  rw [← isOpen_compl_iff]
  have heq : (mrowkaRemainder 𝒜)ᶜ = ⋃ n : ℕ, ({Sum.inl n} : Set (Mrowka 𝒜)) := by
    ext p
    cases p <;> simp [mrowkaRemainder]
  rw [heq]
  exact isOpen_iUnion mrowka_isOpen_singleton

theorem mrowka_remainder_discreteTopology : DiscreteTopology (mrowkaRemainder 𝒜) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  rintro ⟨p, A, rfl⟩
  have heq : ((↑) : mrowkaRemainder 𝒜 → Mrowka 𝒜) ⁻¹'
      mrowkaNeighborhood 𝒜 A ∅ = {⟨Sum.inr A, ⟨A, rfl⟩⟩} := by
    ext q
    rcases q with ⟨q, B, rfl⟩
    simp
  rw [← heq]
  exact (mrowka_isOpen_neighborhood A ∅).preimage continuous_subtype_val

theorem mrowka_compact_meets_remainder_finitely {K : Set (Mrowka 𝒜)} (hK : IsCompact K) :
    Set.Finite ((Sum.inr : 𝒜 → Mrowka 𝒜) ⁻¹' K) := by
  letI := mrowka_remainder_discreteTopology (𝒜 := 𝒜)
  have hf := tendsto_cofinite_cocompact_iff.mp
    ((mrowka_remainder_isClosed (𝒜 := 𝒜)).tendsto_coe_cofinite_of_discreteTopology
      inferInstance) K hK
  let j : 𝒜 → mrowkaRemainder 𝒜 := fun A => ⟨Sum.inr A, ⟨A, rfl⟩⟩
  have hj : Function.Injective j := by
    intro A B hAB
    exact Sum.inr.inj (congrArg Subtype.val hAB)
  change Set.Finite (j ⁻¹' (((↑) : mrowkaRemainder 𝒜 → Mrowka 𝒜) ⁻¹' K))
  exact hf.preimage hj.injOn

theorem mrowka_countable_family_of_secondCountable [SecondCountableTopology (Mrowka 𝒜)] :
    Countable 𝒜 := by
  letI := mrowka_remainder_discreteTopology (𝒜 := 𝒜)
  haveI : Countable (mrowkaRemainder 𝒜) := separableSpace_iff_countable.mp inferInstance
  let j : 𝒜 → mrowkaRemainder 𝒜 := fun A => ⟨Sum.inr A, ⟨A, rfl⟩⟩
  have hj : Function.Injective j := by
    intro A B hAB
    exact Sum.inr.inj (congrArg Subtype.val hAB)
  obtain ⟨f, hf⟩ := exists_injective_nat (mrowkaRemainder 𝒜)
  exact ⟨⟨f ∘ j, hf.comp hj⟩⟩

theorem mrowka_nonmetrizable (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜) :
    ¬ MetrizableSpace (Mrowka 𝒜) := by
  intro hm
  letI := hm
  letI := mrowka_separableSpace h𝒜
  letI := TopologicalSpace.metrizableSpaceMetric (Mrowka 𝒜)
  haveI : Countable 𝒜 := mrowka_countable_family_of_secondCountable
  obtain ⟨e⟩ := hc
  obtain ⟨f, hf⟩ := exists_injective_nat 𝒜
  exact Function.cantor_injective (f ∘ e.symm) (hf.comp e.symm.injective)

end JFA
