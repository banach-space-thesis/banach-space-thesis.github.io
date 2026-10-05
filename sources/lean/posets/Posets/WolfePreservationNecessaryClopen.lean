import Posets.WolfePreservationNecessaryOverlap
import Mathlib.Topology.LocallyConstant.Algebra

/-! A countable family of clopen sets of uniformly finite multiplicity admits
a finite decomposition into disjoint clopen families. The colour records the
number of earlier occurrences, so it depends on only finitely many clopen
membership tests. No such topological conclusion is asserted for arbitrary
coordinate sets. -/

noncomputable section
open Set Filter Topology
namespace Posets

def wolfeClopenOccurrence {K : Type*} (U : ℕ → Set K) (n : ℕ) (x : K) : ℕ := by
  classical
  exact ((Finset.range n).filter fun i => x ∈ U i).card

theorem wolfeClopenOccurrence_continuous {K : Type*} [TopologicalSpace K]
    (U : ℕ → Set K) (hU : ∀ n, IsClopen (U n)) (n : ℕ) :
    Continuous (wolfeClopenOccurrence U n) := by
  classical
  have he : wolfeClopenOccurrence U n =
      fun x => ∑ i ∈ Finset.range n, LocallyConstant.charFn ℕ (hU i) x := by
    funext x
    simp [wolfeClopenOccurrence, LocallyConstant.coe_charFn, Set.indicator_apply,
      Finset.sum_boole]
  rw [he]
  exact continuous_finset_sum _ fun i _ => (LocallyConstant.charFn ℕ (hU i)).continuous

theorem wolfeClopenOccurrence_strict {K : Type*} (U : ℕ → Set K)
    {n m : ℕ} {x : K} (hnm : n < m) (hxn : x ∈ U n) :
    wolfeClopenOccurrence U n x < wolfeClopenOccurrence U m x := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset_filter _ (Finset.range_mono hnm.le), ?_⟩
  intro he
  have hm : n ∈ (Finset.range m).filter fun i => x ∈ U i := by simp [hnm, hxn]
  rw [← he] at hm
  simp at hm

theorem wolfe_clopen_finite_overlap_coloring {K : Type*} [TopologicalSpace K]
    (U : ℕ → Set K) (hU : ∀ n, IsClopen (U n)) (N : ℕ)
    (hN : ∀ x : K, ∀ s : Finset ℕ, (∀ n ∈ s, x ∈ U n) → s.card ≤ N) :
    ∃ D : Fin N → ℕ → Set K,
      (∀ i n, IsClopen (D i n)) ∧
      (∀ n, U n = ⋃ i, D i n) ∧
      (∀ i, Pairwise (fun n m => Disjoint (D i n) (D i m))) ∧
      (∀ n, Pairwise (fun i j => Disjoint (D i n) (D j n))) := by
  classical
  let D (i : Fin N) (n : ℕ) := U n ∩ {x | wolfeClopenOccurrence U n x = i.val}
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro i n
    exact (hU n).inter ((isClopen_discrete {i.val}).preimage
      (wolfeClopenOccurrence_continuous U hU n))
  · intro n
    ext x
    constructor
    · intro hx
      let s := (Finset.range n).filter fun j => x ∈ U j
      have hn : n ∉ s := by simp [s]
      have hbound : (insert n s).card ≤ N := hN x (insert n s) (by
        intro j hj
        obtain rfl | hj := Finset.mem_insert.mp hj
        · exact hx
        · exact (Finset.mem_filter.mp hj).2)
      rw [Finset.card_insert_of_notMem hn] at hbound
      have hlt : wolfeClopenOccurrence U n x < N := by
        change s.card < N
        omega
      exact mem_iUnion.mpr ⟨⟨_, hlt⟩, hx, rfl⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hi.1
  · intro i n m hnm
    apply disjoint_left.mpr
    rintro x ⟨hxn, hcn⟩ ⟨hxm, hcm⟩
    change wolfeClopenOccurrence U n x = i.val at hcn
    change wolfeClopenOccurrence U m x = i.val at hcm
    rcases lt_or_gt_of_ne hnm with hlt | hlt
    · have h := wolfeClopenOccurrence_strict U hlt hxn
      omega
    · have h := wolfeClopenOccurrence_strict U hlt hxm
      omega
  · intro n i j hij
    apply disjoint_left.mpr
    rintro x ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (Fin.ext (hi.symm.trans hj))

end Posets
