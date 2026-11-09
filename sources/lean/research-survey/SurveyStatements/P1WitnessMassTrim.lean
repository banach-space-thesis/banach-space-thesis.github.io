import SurveyStatements.P1PhaseSectors

/-! Trimming a finite witness to bound its mass by its first remaining
coordinate, while losing at most a factor two in total mass. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace SurveyStatements.P1

def witnessMassBudget (k : ℕ) : ℕ := (k + 4) ^ 2

theorem witnessMassBudget_monotone : Monotone witnessMassBudget := by
  intro k m hkm
  dsimp [witnessMassBudget]
  nlinarith

theorem witnessMassBudget_previous (k : ℕ) (hk : 0 < k) :
    k + 1 + witnessMassBudget k ≤ 2 * witnessMassBudget (k - 1) := by
  cases k with
  | zero => omega
  | succ k =>
    simp only [Nat.succ_sub_one]
    dsimp [witnessMassBudget]
    nlinarith

theorem finite_weighted_head_tail_bound (F : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ F, w i ≤ 1) (k : ℕ) :
    ∑ i ∈ F, w i ≤ (k + 1 : ℕ) + ∑ i ∈ F with k < i, w i := by
  let H := F.filter (fun i => i ≤ k)
  have hH : H ⊆ Finset.range (k + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2)
  have hsum : ∑ i ∈ H, w i ≤ (k + 1 : ℕ) := by
    calc
      _ ≤ ∑ i ∈ H, (1 : ℝ) := Finset.sum_le_sum (fun i hi => hw i (Finset.mem_filter.mp hi).1)
      _ = (H.card : ℝ) := by simp
      _ ≤ (k + 1 : ℕ) := by
        exact_mod_cast (show H.card ≤ k + 1 by
          simpa only [Finset.card_range] using Finset.card_le_card hH)
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun i => i ≤ k) w
  have htail : F.filter (fun i => ¬ i ≤ k) = F.filter (fun i => k < i) := by
    ext i
    simp
  rw [htail] at hsplit
  rw [← hsplit]
  exact add_le_add_right hsum _

theorem finite_weighted_tail_trim (F : Finset ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ i ∈ F, 0 ≤ w i) (hw1 : ∀ i ∈ F, w i ≤ 1)
    (hmass : 0 < ∑ i ∈ F, w i) :
    ∃ k : ℕ, ∃ S : Finset ℕ, S = F.filter (fun i => k ≤ i) ∧ S.Nonempty ∧
      (∑ i ∈ F, w i) ≤ 2 * ∑ i ∈ S, w i ∧
      (∑ i ∈ S, w i) ≤ (witnessMassBudget k : ℝ) + 1 ∧
      ∀ i ∈ S, k ≤ i := by
  let P : ℕ → Prop := fun k =>
    ∑ i ∈ F with k < i, w i ≤ (witnessMassBudget k : ℝ)
  have hex : ∃ k, P k := by
    refine ⟨F.sup id, ?_⟩
    have hfilter : F.filter (fun i => F.sup id < i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hiF, hi⟩ := Finset.mem_filter.mp hi
      exact (not_lt_of_ge (Finset.le_sup (f := id) hiF)) hi
    dsimp [P]
    rw [hfilter, Finset.sum_empty]
    positivity
  let k := Nat.find hex
  let S := F.filter (fun i => k ≤ i)
  have hk : P k := Nat.find_spec hex
  have hmassS : 0 < ∑ i ∈ S, w i := by
    by_cases hk0 : k = 0
    · simpa [S, hk0] using hmass
    · have hprev : ¬ P (k - 1) := Nat.find_min hex (by dsimp [k]; omega)
      have hfilter : F.filter (fun i => k - 1 < i) = S := by
        ext i
        constructor
        · intro hi
          obtain ⟨hiF, hki⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨hiF, by omega⟩
        · intro hi
          obtain ⟨hiF, hki⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨hiF, by omega⟩
      have hstrict : (witnessMassBudget (k - 1) : ℝ) < ∑ i ∈ S, w i := by
        simpa only [P, hfilter] using lt_of_not_ge hprev
      exact lt_of_le_of_lt (by positivity) hstrict
  have hretain : (∑ i ∈ F, w i) ≤ 2 * ∑ i ∈ S, w i := by
    by_cases hk0 : k = 0
    · have hSF : S = F := by simp [S, hk0]
      rw [hSF]
      linarith
    · have hprev : ¬ P (k - 1) := Nat.find_min hex (by dsimp [k]; omega)
      have hfilter : F.filter (fun i => k - 1 < i) = S := by
        ext i
        constructor
        · intro hi
          obtain ⟨hiF, hki⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨hiF, by omega⟩
        · intro hi
          obtain ⟨hiF, hki⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨hiF, by omega⟩
      have hstrict : (witnessMassBudget (k - 1) : ℝ) < ∑ i ∈ S, w i := by
        simpa only [P, hfilter] using lt_of_not_ge hprev
      have hrec : (k + 1 : ℕ) + (witnessMassBudget k : ℝ) ≤
          2 * (witnessMassBudget (k - 1) : ℝ) := by
        exact_mod_cast witnessMassBudget_previous k (by omega)
      exact (finite_weighted_head_tail_bound F w hw1 k).trans
        ((add_le_add_left hk (k + 1 : ℕ)).trans (hrec.trans (by linarith)))
  have hupper : (∑ i ∈ S, w i) ≤ (witnessMassBudget k : ℝ) + 1 := by
    have hhead : S.filter (fun i => i ≤ k) ⊆ {k} := by
      intro i hi
      obtain ⟨hiS, hik⟩ := Finset.mem_filter.mp hi
      have hki := (Finset.mem_filter.mp hiS).2
      exact Finset.mem_singleton.mpr (le_antisymm hik hki)
    have hheads : ∑ i ∈ S with i ≤ k, w i ≤ 1 := by
      calc
        _ ≤ ∑ i ∈ S with i ≤ k, (1 : ℝ) := Finset.sum_le_sum fun i hi =>
          hw1 i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        _ = ((S.filter (fun i => i ≤ k)).card : ℝ) := by simp
        _ ≤ 1 := by exact_mod_cast (Finset.card_le_card hhead)
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun i => i ≤ k) w
    have htail : S.filter (fun i => ¬ i ≤ k) = F.filter (fun i => k < i) := by
      ext i
      constructor
      · intro hi
        obtain ⟨hiS, hik⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiF, hki⟩ := Finset.mem_filter.mp hiS
        exact Finset.mem_filter.mpr ⟨hiF, by omega⟩
      · intro hi
        obtain ⟨hiF, hki⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiF, by omega⟩, by omega⟩
    rw [htail] at hsplit
    rw [← hsplit]
    exact (add_le_add hheads hk).trans (by linarith)
  have hS : S.Nonempty := by
    by_contra h
    have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hzero, Finset.sum_empty] at hmassS
    exact (lt_irrefl _) hmassS
  exact ⟨k, S, rfl, hS, hretain, hupper, fun i hi => (Finset.mem_filter.mp hi).2⟩

end SurveyStatements.P1
