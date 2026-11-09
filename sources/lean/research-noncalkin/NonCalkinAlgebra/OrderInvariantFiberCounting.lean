import NonCalkinAlgebra.MetricCardinality

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderInvariantCounting
universe u

/-- The membership-fiber counting step used in Farah--Shelah, Lemma L.trivial.
The cardinal is infinite, as in its nonstructure applications. Distinct sets
are needed because the empty set can occur at most once. -/
theorem exists_large_membership_fiber {A I : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hA : Cardinal.mk A ≤ κ) (hI : κ < Cardinal.mk I)
    (s : I → Set A) (hs : Function.Injective s) :
    ∃ a : A, κ < Cardinal.mk {i : I | a ∈ s i} := by
  classical
  by_contra! hfiber
  have hbound : Cardinal.mk (⋃ a : A, {i : I | a ∈ s i}) ≤ κ := by
    calc
      _ ≤ Cardinal.sum (fun a : A => Cardinal.mk {i : I | a ∈ s i}) :=
        Cardinal.mk_iUnion_le_sum_mk
      _ ≤ Cardinal.sum (fun _ : A => κ) := Cardinal.sum_le_sum _ _ hfiber
      _ = Cardinal.mk A * κ := Cardinal.sum_const' A κ
      _ ≤ κ * κ := mul_le_mul' hA le_rfl
      _ = κ := Cardinal.mul_eq_self hκ
  have hempty : {i : I | s i = ∅}.Subsingleton := by
    intro i hi j hj
    exact hs (hi.trans hj.symm)
  have hemptyBound : Cardinal.mk {i : I | s i = ∅} ≤ κ :=
    hempty.cardinalMk_le_one.trans (Cardinal.one_le_aleph0.trans hκ)
  have hcover : (Set.univ : Set I) = {i : I | s i = ∅} ∪ ⋃ a : A, {i : I | a ∈ s i} := by
    ext i
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro _
      by_cases hi : s i = ∅
      · exact Or.inl hi
      · exact Or.inr (Set.nonempty_iff_ne_empty.mpr hi)
    · intro _
      trivial
  have hsmall : Cardinal.mk I ≤ κ := by
    calc
      Cardinal.mk I = Cardinal.mk (Set.univ : Set I) := Cardinal.mk_univ.symm
      _ = Cardinal.mk (({i : I | s i = ∅} ∪ ⋃ a : A, {i : I | a ∈ s i}) : Set I) := by
        rw [hcover]
      _ ≤ Cardinal.mk {i : I | s i = ∅} + Cardinal.mk (⋃ a : A, {i : I | a ∈ s i}) :=
        Cardinal.mk_union_le _ _
      _ ≤ κ + κ := add_le_add hemptyBound hbound
      _ = κ := Cardinal.add_eq_self hκ
  exact (not_le_of_gt hI) hsmall

/-- In particular, a family of distinct subsets of a continuum-sized set
larger than continuum has a coordinate in more than continuum many members. -/
theorem exists_continuum_large_membership_fiber {A I : Type}
    (hA : Cardinal.mk A ≤ Cardinal.continuum) (hI : Cardinal.continuum < Cardinal.mk I)
    (s : I → Set A) (hs : Function.Injective s) :
    ∃ a : A, Cardinal.continuum < Cardinal.mk {i : I | a ∈ s i} :=
  exists_large_membership_fiber Cardinal.aleph0_le_continuum hA hI s hs

end NonCalkinAlgebra.OrderInvariantCounting
