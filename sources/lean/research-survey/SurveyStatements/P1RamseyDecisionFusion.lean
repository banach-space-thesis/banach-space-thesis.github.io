import SurveyStatements.P1RamseyDecisions
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset

/-! Infinite decision fusion for finite prefixes.  The recursive state records
an actual finite front and an actual infinite tail; every choice is justified
by finite-family refinement. -/

noncomputable section
set_option autoImplicit false
open Set

namespace SurveyStatements.P1

private structure RamseyDecisionStage (P : Finset ℕ → Prop) (M : Set ℕ) where
  front : Finset ℕ
  tail : Set ℕ
  infinite_tail : tail.Infinite
  tail_subset : tail ⊆ M
  after_prefix : ∀ a ∈ front, ∀ b ∈ tail, a < b
  decisions : ∀ s ⊆ front, RamseyDecides P s tail

private theorem RamseyDecisionStage.exists_initial (P : Finset ℕ → Prop)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ q : RamseyDecisionStage P M, q.front = ∅ := by
  obtain ⟨N, hNM, hN, hdec⟩ := exists_infinite_subset_ramseyDecides P ∅ M hM
  refine ⟨⟨∅, N, hN, hNM, ?_, ?_⟩, rfl⟩
  · simp
  · intro s hs
    have : s = ∅ := Finset.subset_empty.mp hs
    simpa only [this] using hdec

private theorem RamseyDecisionStage.exists_next {P : Finset ℕ → Prop} {M : Set ℕ}
    (q : RamseyDecisionStage P M) :
    ∃ n : ℕ, ∃ r : RamseyDecisionStage P M,
      n ∈ q.tail ∧ r.front = insert n q.front ∧ r.tail ⊆ q.tail := by
  classical
  obtain ⟨n, hn⟩ := q.infinite_tail.nonempty
  obtain ⟨N, hNsub, hNinf, hNdec⟩ :=
    exists_infinite_subset_decides_finite_family P (insert n q.front).powerset
      (q.tail ∩ Ioi n) (infiniteSet_inter_Ioi q.tail q.infinite_tail n)
  let r : RamseyDecisionStage P M :=
    { front := insert n q.front
      tail := N
      infinite_tail := hNinf
      tail_subset := fun b hb => q.tail_subset (hNsub hb).1
      after_prefix := by
        intro a ha b hb
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact (hNsub hb).2
        · exact q.after_prefix a ha b (hNsub hb).1
      decisions := fun s hs => hNdec s (Finset.mem_powerset.mpr hs) }
  exact ⟨n, r, hn, rfl, fun b hb => (hNsub hb).1⟩

theorem ramsey_exists_decision_fusion (P : Finset ℕ → Prop) (M : Set ℕ)
    (hM : M.Infinite) :
    ∃ ν : ℕ → ℕ, ∃ T : ℕ → Set ℕ,
      StrictMono ν ∧ (∀ n, ν n ∈ M) ∧ (∀ n, (T n).Infinite) ∧
      (∀ n, T (n + 1) ⊆ T n) ∧
      (∀ n k, n ≤ k → ν k ∈ T n) ∧
      (∀ n s, s ⊆ (Finset.range n).image ν → RamseyDecides P s (T n)) := by
  classical
  obtain ⟨q₀, hq₀⟩ := RamseyDecisionStage.exists_initial P M hM
  let step (q : RamseyDecisionStage P M) : ℕ × RamseyDecisionStage P M :=
    ⟨(RamseyDecisionStage.exists_next q).choose,
      ((RamseyDecisionStage.exists_next q).choose_spec).choose⟩
  have hs (q : RamseyDecisionStage P M) :
      (step q).1 ∈ q.tail ∧ (step q).2.front = insert (step q).1 q.front ∧
        (step q).2.tail ⊆ q.tail :=
    ((RamseyDecisionStage.exists_next q).choose_spec).choose_spec
  let q : ℕ → RamseyDecisionStage P M := Nat.rec q₀ (fun _ r => (step r).2)
  let ν : ℕ → ℕ := fun n => (step (q n)).1
  have hrec (n : ℕ) : q (n + 1) = (step (q n)).2 := rfl
  have hmem (n : ℕ) : ν n ∈ (q n).tail := (hs (q n)).1
  have hprefix (n : ℕ) : (q n).front = (Finset.range n).image ν := by
    induction n with
    | zero => simpa only [q, Finset.range_zero, Finset.image_empty] using hq₀
    | succ n ih =>
      rw [hrec, (hs (q n)).2.1, ih, Finset.range_add_one, Finset.image_insert]
  have hν : StrictMono ν := by
    apply strictMono_nat_of_lt_succ
    intro n
    apply (q (n + 1)).after_prefix (ν n) _ (ν (n + 1)) (hmem (n + 1))
    rw [hrec, (hs (q n)).2.1]
    exact Finset.mem_insert_self _ _
  have hnest (n : ℕ) : (q (n + 1)).tail ⊆ (q n).tail := by
    rw [hrec]
    exact (hs (q n)).2.2
  have hanti : Antitone (fun n => (q n).tail) := antitone_nat_of_succ_le hnest
  refine ⟨ν, fun n => (q n).tail, hν,
    fun n => (q n).tail_subset (hmem n), fun n => (q n).infinite_tail,
    hnest, fun n k hnk => hanti hnk (hmem k), ?_⟩
  intro n s hs
  apply (q n).decisions s
  simpa only [hprefix] using hs

theorem exists_infinite_subset_decides_all_prefixes (P : Finset ℕ → Prop)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ L → RamseyDecides P s L := by
  classical
  obtain ⟨ν, T, hν, hνM, hTinf, hnest, htail, hdec⟩ :=
    ramsey_exists_decision_fusion P M hM
  let L : Set ℕ := range ν
  have hL : L.Infinite := Set.infinite_range_of_injective hν.injective
  have hLT₀ : L ⊆ T 0 := by
    rintro _ ⟨k, rfl⟩
    exact htail 0 k (Nat.zero_le k)
  refine ⟨L, ?_, hL, ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact hνM k
  · intro s hs
    by_cases he : s = ∅
    · subst s
      exact (hdec 0 ∅ (by simp)).mono hLT₀
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
      have hmax : s.sup id ∈ s := by
        obtain ⟨a, ha, heq⟩ := s.sup_mem_of_nonempty hne (f := id)
        exact heq ▸ ha
      obtain ⟨k, hk⟩ := hs hmax
      have hspre : s ⊆ (Finset.range (k + 1)).image ν := by
        intro a ha
        obtain ⟨i, hi⟩ := hs ha
        have hia : i ≤ k := hν.le_iff_le.mp (by
          rw [hi, hk]
          exact Finset.le_sup (f := id) ha)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hia), hi⟩
      apply RamseyDecides.transfer_tail hmax _ (hdec (k + 1) s hspre)
      intro a ha hmaxa
      obtain ⟨i, rfl⟩ := ha
      have hki : k < i := hν.lt_iff_lt.mp (by simpa only [hk] using hmaxa)
      exact htail (k + 1) i (Nat.succ_le_of_lt hki)

end SurveyStatements.P1
