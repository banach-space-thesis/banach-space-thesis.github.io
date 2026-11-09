import SurveyStatements.P1RamseyDecisionFusion
import Mathlib.Data.Set.Finite.Lattice

/-! The elementary closed Ramsey theorem, in finite-set front form.  This
is the combinatorial selection theorem of Behrends, Section 2. -/

noncomputable section
set_option autoImplicit false
open Set

namespace SurveyStatements.P1

theorem ramsey_accepted_prefix_exists_extension (P : Finset ℕ → Prop)
    (M : Set ℕ) (hM : M.Infinite)
    (hdec : ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → RamseyDecides P s M)
    (p : Finset ℕ) (hpM : (↑p : Set ℕ) ⊆ M)
    (hp : ∀ s ⊆ p, RamseyAccepts P s M) :
    ∃ n ∈ M, p.sup id < n ∧ ∀ t ⊆ insert n p, RamseyAccepts P t M := by
  classical
  let B : Set ℕ := ⋃ s ∈ (↑p.powerset : Set (Finset ℕ)),
    {n : ℕ | n ∈ M ∧ RamseyRejects P (insert n s) M}
  have hB : B.Finite := p.powerset.finite_toSet.biUnion (fun s hs =>
    (hp s (Finset.mem_powerset.mp hs)).finite_rejected_extensions)
  obtain ⟨n, hn, hnlarge⟩ := (hM.diff hB).exists_gt (p.sup id)
  refine ⟨n, hn.1, hnlarge, ?_⟩
  intro t ht
  have htM : (↑t : Set ℕ) ⊆ M := by
    intro a ha
    rcases Finset.mem_insert.mp (ht ha) with rfl | hap
    · exact hn.1
    · exact hpM hap
  by_cases hnt : n ∈ t
  · have hErase : t.erase n ⊆ p := by
      intro a ha
      have hane : a ≠ n := (Finset.mem_erase.mp ha).1
      rcases Finset.mem_insert.mp (ht (Finset.mem_erase.mp ha).2) with han | hap
      · exact False.elim (hane han)
      · exact hap
    have hnot : ¬ RamseyRejects P t M := by
      intro hrej
      apply hn.2
      apply Set.mem_iUnion.mpr
      refine ⟨t.erase n, Set.mem_iUnion.mpr ?_⟩
      refine ⟨Finset.mem_powerset.mpr hErase, hn.1, ?_⟩
      simpa only [Finset.insert_erase hnt] using hrej
    exact (hdec t htM).resolve_right hnot
  · apply hp t
    intro a ha
    rcases Finset.mem_insert.mp (ht ha) with han | hap
    · exact False.elim (hnt (han ▸ ha))
    · exact hap

private structure RamseyAcceptedPrefix (P : Finset ℕ → Prop) (M : Set ℕ) where
  front : Finset ℕ
  subset : (↑front : Set ℕ) ⊆ M
  accepts : ∀ s ⊆ front, RamseyAccepts P s M

theorem ramsey_acceptance_exists_good_sequence (P : Finset ℕ → Prop)
    (M : Set ℕ) (hM : M.Infinite)
    (hdec : ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → RamseyDecides P s M)
    (hacc : RamseyAccepts P ∅ M) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ (∀ n, ν n ∈ M) ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ range ν → P s := by
  classical
  let initial : RamseyAcceptedPrefix P M :=
    { front := ∅
      subset := by simp
      accepts := by
        intro s hs
        have : s = ∅ := Finset.subset_empty.mp hs
        simpa only [this] using hacc }
  have hex (q : RamseyAcceptedPrefix P M) :=
    ramsey_accepted_prefix_exists_extension P M hM hdec q.front q.subset q.accepts
  let next (q : RamseyAcceptedPrefix P M) : ℕ := (hex q).choose
  have hnext (q : RamseyAcceptedPrefix P M) :
      next q ∈ M ∧ q.front.sup id < next q ∧
        ∀ t ⊆ insert (next q) q.front, RamseyAccepts P t M := (hex q).choose_spec
  let step (q : RamseyAcceptedPrefix P M) : RamseyAcceptedPrefix P M :=
    { front := insert (next q) q.front
      subset := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact (hnext q).1
        · exact q.subset ha
      accepts := (hnext q).2.2 }
  let q : ℕ → RamseyAcceptedPrefix P M := Nat.rec initial (fun _ r => step r)
  let ν : ℕ → ℕ := fun n => next (q n)
  have hrec (n : ℕ) : (q (n + 1)).front = insert (ν n) (q n).front := rfl
  have hprefix (n : ℕ) : (q n).front = (Finset.range n).image ν := by
    induction n with
    | zero => rfl
    | succ n ih => rw [hrec, ih, Finset.range_add_one, Finset.image_insert]
  have hν : StrictMono ν := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hn : ν n ∈ (q (n + 1)).front := by
      rw [hrec]
      exact Finset.mem_insert_self _ _
    exact (Finset.le_sup (f := id) hn).trans_lt (hnext (q (n + 1))).2.1
  have hid (n : ℕ) : n ≤ ν n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hν (Nat.lt_succ_self n)))
  refine ⟨ν, hν, fun n => (hnext (q n)).1, ?_⟩
  intro s hs
  have hsp : s ⊆ (q (s.sup id + 1)).front := by
    rw [hprefix (s.sup id + 1)]
    intro a ha
    obtain ⟨i, hi⟩ := hs ha
    have hiN : i < s.sup id + 1 := Nat.lt_succ_of_le
      ((hid i).trans (by rw [hi]; exact Finset.le_sup (f := id) ha))
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hiN, hi⟩
  exact ((q (s.sup id + 1)).accepts s hsp).good hM

theorem closedRamsey_exists_infinite_good_subset (P : Finset ℕ → Prop)
    (M : Set ℕ) (hM : M.Infinite) (hbranch : RamseyAccepts P ∅ M) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ L → P s := by
  obtain ⟨N, hNM, hN, hdec⟩ := exists_infinite_subset_decides_all_prefixes P M hM
  obtain ⟨ν, hν, hνN, hgood⟩ :=
    ramsey_acceptance_exists_good_sequence P N hN hdec (hbranch.mono hNM)
  refine ⟨range ν, ?_, Set.infinite_range_of_injective hν.injective, hgood⟩
  rintro _ ⟨n, rfl⟩
  exact hNM (hνN n)

theorem closedRamsey_from_infinite_branches (P : Finset ℕ → Prop)
    (M : Set ℕ) (hM : M.Infinite)
    (hbranch : ∀ N : Set ℕ, N ⊆ M → N.Infinite →
      ∃ ν : ℕ → ℕ, StrictMono ν ∧ (∀ n, ν n ∈ N) ∧
        ∀ n, P ((Finset.range n).image ν)) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ L → P s := by
  apply closedRamsey_exists_infinite_good_subset P M hM
  intro N hNM hN
  obtain ⟨ν, hν, hνN, hP⟩ := hbranch N hNM hN
  exact ⟨ν, hν, by simp, fun n _ => hνN n, hP⟩

end SurveyStatements.P1
