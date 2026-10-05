import ThesisCommon.Analysis.HajnalCofinality

/-! Cardinal partition and tail-selection tools for the singular branch of
Hajnal's theorem. These are preparatory lemmas, not the full free-set theorem. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ : Type u}

/-- An infinite set has ν disjoint subsets each of its full cardinality,
whenever 0 < ν ≤ its cardinality. -/
theorem exists_fullCardinality_partition (S : Set Γ) (ν : Cardinal.{u})
    (hS : Cardinal.aleph0 ≤ Cardinal.mk S) (hνpos : 0 < ν)
    (hν : ν ≤ Cardinal.mk S) :
    ∃ A : ν.ord.toType → Set Γ,
      (∀ i, A i ⊆ S) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ i, Cardinal.mk (A i) = Cardinal.mk S) ∧ (⋃ i, A i) = S := by
  classical
  have hprod : Cardinal.mk (ν.ord.toType × S) = Cardinal.mk S := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_ord_toType,
      Cardinal.mul_eq_max_of_aleph0_le_right hνpos.ne' hS, max_eq_right hν]
  obtain ⟨e⟩ := Cardinal.eq.mp hprod
  let f (i : ν.ord.toType) (x : S) : Γ := (e (i, x)).val
  have hf (i : ν.ord.toType) : Function.Injective (f i) := by
    intro x y h
    have he : e (i, x) = e (i, y) := Subtype.ext h
    exact congrArg Prod.snd (e.injective he)
  refine ⟨fun i => Set.range (f i), ?_, ?_, ?_, ?_⟩
  · rintro i _ ⟨x, rfl⟩
    exact (e (i, x)).property
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    apply hij
    exact (congrArg Prod.fst (e.injective (Subtype.ext hy))).symm
  · intro i
    exact Cardinal.mk_range_eq (f i) (hf i)
  · apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨i, rfl⟩, x, rfl⟩
      exact (e (i, x)).property
    · intro x hx
      let z := e.symm ⟨x, hx⟩
      apply Set.mem_iUnion.mpr
      refine ⟨z.1, Set.mem_range.mpr ⟨z.2, ?_⟩⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

/-- A set can meet no more disjoint pieces than its own cardinality. -/
theorem mk_disjoint_hits_le {ι : Type u} (A : ι → Set Γ)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (B : Set Γ) :
    Cardinal.mk {i | (B ∩ A i).Nonempty} ≤ Cardinal.mk B := by
  classical
  let J := {i | (B ∩ A i).Nonempty}
  let f : J → B := fun i => ⟨i.property.choose, i.property.choose_spec.1⟩
  have hf (i : J) : (f i).val ∈ A i.val := i.property.choose_spec.2
  apply Cardinal.mk_le_of_injective (f := f)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  apply Set.disjoint_left.mp (hA hne) (hf i)
  rw [show (f i).val = (f j).val from congrArg Subtype.val hij]
  exact hf j

/-- Fewer than ν points miss a tail of a ν-indexed disjoint family when ν
is regular. The tail conclusion uses ≥ and is valid for all points of B. -/
theorem exists_disjoint_tail (ν : Cardinal.{u}) (hν : ν.IsRegular)
    (A : ν.ord.toType → Set Γ)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (B : Set Γ) (hB : Cardinal.mk B < ν) :
    ∃ i : ν.ord.toType, ∀ j, i ≤ j → Disjoint B (A j) := by
  let J : Set ν.ord.toType := {i | (B ∩ A i).Nonempty}
  have hJ : Cardinal.mk J < ν := (mk_disjoint_hits_le A hA B).trans_lt hB
  have hcof : Cardinal.mk J < (Ordinal.type ((· < ·) : ν.ord.toType → _ → Prop)).cof := by
    simpa only [Ordinal.type_toType, hν.cof_eq] using hJ
  obtain ⟨i, hi⟩ := Ordinal.lt_cof_type (r := ((· < ·) : ν.ord.toType → _ → Prop)) hcof
  refine ⟨i, fun j hij => Set.disjoint_left.mpr ?_⟩
  intro x hxB hxA
  exact (hi j ⟨x, hxB, hxA⟩).not_ge hij

/-- Pigeonhole on a regular-sized subset, with an actual same-sized fibre
inside the original ambient type. -/
theorem exists_fullCardinality_constant_subset {ι : Type u} (S : Set Γ)
    (hS : (Cardinal.mk S).IsRegular) (hι : Cardinal.mk ι < Cardinal.mk S)
    (f : S → ι) :
    ∃ (i : ι) (A : Set Γ) (hAS : A ⊆ S), Cardinal.mk A = Cardinal.mk S ∧
      ∀ x (hx : x ∈ A), f ⟨x, hAS hx⟩ = i := by
  obtain ⟨i, A, hAS, hcard, hf⟩ := Cardinal.infinite_pigeonhole_set f
    (Cardinal.mk S) le_rfl hS.aleph0_le (by simpa only [hS.cof_eq] using hι)
  refine ⟨i, A, hAS, hcard.antisymm' (Cardinal.mk_le_mk_of_subset hAS), ?_⟩
  intro x hx
  exact hf hx

end ThesisCommon
