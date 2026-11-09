import SurveyStatements.P1RamseyFusion

/-! Acceptance and rejection of finite prefixes in the elementary closed
Ramsey argument (Behrends, arXiv:math/9403211, Section 2).
Continuation branches are actual strictly increasing sequences; no Ramsey
selection premise is encoded in the definitions. -/

noncomputable section
set_option autoImplicit false
open Set

namespace SurveyStatements.P1

def RamseyCanExtend (P : Finset ℕ → Prop) (s : Finset ℕ) (M : Set ℕ) : Prop :=
  ∃ ν : ℕ → ℕ, StrictMono ν ∧ (Finset.range s.card).image ν = s ∧
    (∀ n, s.card ≤ n → ν n ∈ M) ∧
    ∀ n, P ((Finset.range n).image ν)

def RamseyAccepts (P : Finset ℕ → Prop) (s : Finset ℕ) (M : Set ℕ) : Prop :=
  ∀ N : Set ℕ, N ⊆ M → N.Infinite → RamseyCanExtend P s N

def RamseyRejects (P : Finset ℕ → Prop) (s : Finset ℕ) (M : Set ℕ) : Prop :=
  ¬ RamseyCanExtend P s M

def RamseyDecides (P : Finset ℕ → Prop) (s : Finset ℕ) (M : Set ℕ) : Prop :=
  RamseyAccepts P s M ∨ RamseyRejects P s M

theorem RamseyCanExtend.mono {P : Finset ℕ → Prop} {s : Finset ℕ} {M N : Set ℕ}
    (h : RamseyCanExtend P s N) (hNM : N ⊆ M) : RamseyCanExtend P s M := by
  obtain ⟨ν, hν, hfront, htail, hP⟩ := h
  exact ⟨ν, hν, hfront, fun n hn => hNM (htail n hn), hP⟩

theorem RamseyAccepts.mono {P : Finset ℕ → Prop} {s : Finset ℕ} {M N : Set ℕ}
    (h : RamseyAccepts P s M) (hNM : N ⊆ M) : RamseyAccepts P s N :=
  fun L hLN hL => h L (hLN.trans hNM) hL

theorem RamseyRejects.mono {P : Finset ℕ → Prop} {s : Finset ℕ} {M N : Set ℕ}
    (h : RamseyRejects P s M) (hNM : N ⊆ M) : RamseyRejects P s N :=
  fun hN => h (hN.mono hNM)

theorem RamseyDecides.mono {P : Finset ℕ → Prop} {s : Finset ℕ} {M N : Set ℕ}
    (h : RamseyDecides P s M) (hNM : N ⊆ M) : RamseyDecides P s N := by
  rcases h with h | h
  · exact Or.inl (h.mono hNM)
  · exact Or.inr (h.mono hNM)

theorem exists_infinite_subset_ramseyDecides (P : Finset ℕ → Prop) (s : Finset ℕ)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ N : Set ℕ, N ⊆ M ∧ N.Infinite ∧ RamseyDecides P s N := by
  classical
  by_cases h : ∃ N : Set ℕ, N ⊆ M ∧ N.Infinite ∧ RamseyRejects P s N
  · obtain ⟨N, hNM, hN, hrej⟩ := h
    exact ⟨N, hNM, hN, Or.inr hrej⟩
  · refine ⟨M, subset_rfl, hM, Or.inl ?_⟩
    intro N hNM hN
    by_contra hnot
    exact h ⟨N, hNM, hN, hnot⟩

theorem exists_infinite_subset_decides_finite_family (P : Finset ℕ → Prop)
    (A : Finset (Finset ℕ)) (M : Set ℕ) (hM : M.Infinite) :
    ∃ N : Set ℕ, N ⊆ M ∧ N.Infinite ∧ ∀ s ∈ A, RamseyDecides P s N := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨M, subset_rfl, hM, fun s hs => False.elim (Finset.notMem_empty s hs)⟩
  | @insert s A hs ih =>
    obtain ⟨N, hNM, hN, hA⟩ := ih
    obtain ⟨L, hLN, hL, hsL⟩ := exists_infinite_subset_ramseyDecides P s N hN
    refine ⟨L, hLN.trans hNM, hL, ?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hsL
    · exact (hA t ht).mono hLN

theorem RamseyAccepts.good {P : Finset ℕ → Prop} {s : Finset ℕ} {M : Set ℕ}
    (h : RamseyAccepts P s M) (hM : M.Infinite) : P s := by
  obtain ⟨ν, _, hfront, _, hP⟩ := h M subset_rfl hM
  simpa only [hfront] using hP s.card

theorem RamseyCanExtend.next_not_mem {P : Finset ℕ → Prop} {s : Finset ℕ}
    {M : Set ℕ} {ν : ℕ → ℕ} (hν : StrictMono ν)
    (hfront : (Finset.range s.card).image ν = s) : ν s.card ∉ s := by
  intro hn
  have hn' : ν s.card ∈ (Finset.range s.card).image ν := by
    rw [hfront]
    exact hn
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hn'
  have hi' : i < s.card := Finset.mem_range.mp hi
  have : i = s.card := hν.injective heq
  exact (Nat.ne_of_lt hi') this

theorem RamseyCanExtend.tail_gt_member {s : Finset ℕ} {ν : ℕ → ℕ}
    (hν : StrictMono ν) (hfront : (Finset.range s.card).image ν = s)
    {a n : ℕ} (ha : a ∈ s) (hn : s.card ≤ n) : a < ν n := by
  rw [← hfront] at ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  exact hν ((Finset.mem_range.mp hi).trans_le hn)

theorem RamseyCanExtend.insert_next {P : Finset ℕ → Prop} {s : Finset ℕ}
    {M : Set ℕ} {ν : ℕ → ℕ} (hν : StrictMono ν)
    (hfront : (Finset.range s.card).image ν = s)
    (htail : ∀ n, s.card ≤ n → ν n ∈ M)
    (hP : ∀ n, P ((Finset.range n).image ν)) :
    RamseyCanExtend P (insert (ν s.card) s) M := by
  classical
  have hnot := RamseyCanExtend.next_not_mem (P := P) (M := M) hν hfront
  have hcard : (insert (ν s.card) s).card = s.card + 1 := Finset.card_insert_of_notMem hnot
  refine ⟨ν, hν, ?_, ?_, hP⟩
  · rw [hcard, Finset.range_add_one, Finset.image_insert, hfront]
  · intro n hn
    apply htail n
    rw [hcard] at hn
    exact (Nat.le_succ _).trans hn

theorem RamseyAccepts.finite_rejected_extensions {P : Finset ℕ → Prop}
    {s : Finset ℕ} {M : Set ℕ} (h : RamseyAccepts P s M) :
    {n : ℕ | n ∈ M ∧ RamseyRejects P (insert n s) M}.Finite := by
  classical
  by_contra hnot
  let B : Set ℕ := {n | n ∈ M ∧ RamseyRejects P (insert n s) M}
  have hB : B.Infinite := hnot
  obtain ⟨ν, hν, hfront, htail, hP⟩ := h B (fun n hn => hn.1) hB
  have hnB := htail s.card le_rfl
  exact hnB.2 (RamseyCanExtend.insert_next hν hfront
    (fun n hn => (htail n hn).1) hP)

theorem RamseyDecides.transfer_tail {P : Finset ℕ → Prop} {s : Finset ℕ}
    {M L : Set ℕ} {a : ℕ} (ha : a ∈ s)
    (htail : ∀ n ∈ L, a < n → n ∈ M) (h : RamseyDecides P s M) :
    RamseyDecides P s L := by
  rcases h with hacc | hrej
  · left
    intro N hNL hN
    have hNM : N ∩ Ioi a ⊆ M := fun n hn => htail n (hNL hn.1) hn.2
    exact (hacc (N ∩ Ioi a) hNM (infiniteSet_inter_Ioi N hN a)).mono
      (fun n hn => hn.1)
  · right
    rintro ⟨ν, hν, hfront, hνtail, hP⟩
    apply hrej
    refine ⟨ν, hν, hfront, ?_, hP⟩
    intro n hn
    exact htail (ν n) (hνtail n hn)
      (RamseyCanExtend.tail_gt_member hν hfront ha hn)

end SurveyStatements.P1
