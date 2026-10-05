import ThesisCommon.Analysis.OrdinalDerived

/-! The transfinite rank-selection argument for finite closed covers. This is
the derived-set part of finite topological indivisibility; identifying spaces
from their characteristic systems is a separate theorem. -/
noncomputable section
open Set Order
universe u v
namespace ThesisCommon
variable {K : Type v} [TopologicalSpace K] [T1Space K]

@[simp] theorem ordinalDerived_empty (α : Ordinal.{u}) :
    ordinalDerived (∅ : Set K) α = ∅ := by
  induction α using Ordinal.limitRecOn with
  | zero => simp
  | succ α ih =>
      rw [ordinalDerived_succ, ih]
      exact Subset.antisymm (by simpa using derivedSet_subset_closure (∅ : Set K)) (empty_subset _)
  | limit α hα ih =>
      apply Subset.antisymm _ (empty_subset _)
      rw [ordinalDerived_limit ∅ hα]
      exact iInter_subset_of_subset 0 (iInter_subset_of_subset hα.bot_lt (by simp))

theorem ordinalDerived_biUnion_finset {ι : Type*} (s : Finset ι) (A : ι → Set K)
    (hA : ∀ i ∈ s, IsClosed (A i)) (α : Ordinal.{u}) :
    ordinalDerived (⋃ i ∈ s, A i) α = ⋃ i ∈ s, ordinalDerived (A i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
      rw [ordinalDerived_union (hA i (Finset.mem_insert_self _ _))
        (isClosed_biUnion_finset (fun j hj => hA j (Finset.mem_insert_of_mem hj)))]
      rw [ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))]

theorem ordinalDerived_iUnion_finite {ι : Type*} [Finite ι] (A : ι → Set K)
    (hA : ∀ i, IsClosed (A i)) (α : Ordinal.{u}) :
    ordinalDerived (⋃ i, A i) α = ⋃ i, ordinalDerived (A i) α := by
  classical
  letI := Fintype.ofFinite ι
  simpa using ordinalDerived_biUnion_finset Finset.univ A (fun i _ => hA i) α

/-- In a finite closed cover, a singleton transfinite derivative is already
the derivative of one of the members, with no loss of rank. -/
theorem exists_ordinalDerived_eq_singleton_of_finite_cover {ι : Type*} [Finite ι]
    {A : Set K} (B : ι → Set K) (hB : ∀ i, IsClosed (B i))
    (hcover : A = ⋃ i, B i) (α : Ordinal.{u}) {a : K}
    (hα : ordinalDerived A α = {a}) :
    ∃ i, ordinalDerived (B i) α = {a} := by
  have hunion : (⋃ i, ordinalDerived (B i) α) = {a} := by
    rw [← ordinalDerived_iUnion_finite B hB, ← hcover, hα]
  have ha : a ∈ ⋃ i, ordinalDerived (B i) α := by rw [hunion]; exact mem_singleton a
  obtain ⟨i, hi⟩ := mem_iUnion.mp ha
  refine ⟨i, Subset.antisymm ?_ (singleton_subset_iff.mpr hi)⟩
  rw [← hunion]
  exact subset_iUnion (fun j => ordinalDerived (B j) α) i

end ThesisCommon
