import ThesisCommon.Combinatorics.InfiniteRamsey
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete
import Mathlib.Data.Finset.Powerset

/-! The finite finite-color Ramsey theorem, derived from the checked infinite
theorem by compactness of the actual space of finite-color functions. The
result provides a size chosen before the coloring, with no coloring-dependent
bound or assumed homogeneous-selection conclusion. -/
noncomputable section
namespace ThesisCommon

theorem finite_ramsey (C : Type*) [Finite C] (k n : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ c : Finset ℕ → C,
      ∃ s : Finset ℕ, s ⊆ Finset.range N ∧ s.card = n ∧
        ∃ γ : C, FinsetHomogeneous c k (s : Set ℕ) γ := by
  classical
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  let U (s : {s : Finset ℕ // s.card = n}) : Set (Finset ℕ → C) :=
    {c | ∃ γ : C, ∀ u ∈ s.val.powersetCard k, c u = γ}
  have hopen (s : {s : Finset ℕ // s.card = n}) : IsOpen (U s) := by
    have h : IsOpen (⋃ γ : C, ⋂ u ∈ s.val.powersetCard k,
        {c : Finset ℕ → C | c u = γ}) := by
      apply isOpen_iUnion
      intro γ
      apply isOpen_biInter_finset
      intro u _
      exact (isOpen_discrete ({γ} : Set C)).preimage
        (continuous_apply u : Continuous (fun c : Finset ℕ → C => c u))
    convert h using 1
    ext c
    simp [U]
  have hcover : (Set.univ : Set (Finset ℕ → C)) ⊆ ⋃ s, U s := by
    intro c _
    obtain ⟨T, _, hT, γ, hγ⟩ := infinite_ramsey k c (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
    obtain ⟨s, hs, hcard⟩ := hT.exists_subset_card_eq n
    apply Set.mem_iUnion.mpr
    refine ⟨⟨s, hcard⟩, γ, ?_⟩
    intro u hu
    obtain ⟨hus, hucard⟩ := Finset.mem_powersetCard.mp hu
    exact hγ u (fun x hx => hs (hus hx)) hucard
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  let N := t.sup (fun s => s.val.sup id) + 1
  refine ⟨N, Nat.succ_pos _, ?_⟩
  intro c
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ c))
  obtain ⟨hst, γ, hγ⟩ := Set.mem_iUnion.mp hs
  refine ⟨s.val, ?_, s.property, γ, ?_⟩
  · intro i hi
    apply Finset.mem_range.mpr
    have h₁ : i ≤ s.val.sup id := Finset.le_sup (f := id) hi
    have h₂ : s.val.sup id ≤ t.sup (fun s => s.val.sup id) :=
      Finset.le_sup (f := fun s => s.val.sup id) hst
    exact Nat.lt_succ_of_le (h₁.trans h₂)
  · intro u hu hcard
    exact hγ u (Finset.mem_powersetCard.mpr ⟨hu, hcard⟩)

end ThesisCommon
