import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Nat
import Mathlib.Tactic

/-! Ordered enumeration of finite blocks, including empty blocks and finite
total length, by an actual initial segment of the natural numbers. -/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace SurveyStatements.P4

def blockOffset (d : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, d k

@[simp] lemma blockOffset_zero (d : ℕ → ℕ) : blockOffset d 0 = 0 := by simp [blockOffset]

lemma blockOffset_succ (d : ℕ → ℕ) (n : ℕ) :
    blockOffset d (n + 1) = blockOffset d n + d n := Finset.sum_range_succ _ _

lemma blockOffset_monotone (d : ℕ → ℕ) : Monotone (blockOffset d) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [blockOffset_succ]
  omega

def blockIndexSet (d : ℕ → ℕ) : Set ℕ := {k | ∃ n, k < blockOffset d n}

lemma blockIndexSet_isLowerSet (d : ℕ → ℕ) : IsLowerSet (blockIndexSet d) := by
  intro i j hij hj
  obtain ⟨n, hn⟩ := hj
  exact ⟨n, hij.trans_lt hn⟩

def blockEncode (d : ℕ → ℕ) (i : Σ n, Fin (d n)) : blockIndexSet d :=
  ⟨blockOffset d i.1 + i.2.val,
    ⟨i.1 + 1, by rw [blockOffset_succ]; exact Nat.add_lt_add_left i.2.isLt _⟩⟩

lemma blockEncode_injective (d : ℕ → ℕ) : Function.Injective (blockEncode d) := by
  rintro ⟨n, i⟩ ⟨m, j⟩ h
  have heq : blockOffset d n + i.val = blockOffset d m + j.val :=
    congrArg Subtype.val h
  have hi := i.isLt
  have hj := j.isLt
  by_cases hnm : n = m
  · subst m
    have hij : i = j := Fin.ext (by omega)
    subst j
    rfl
  · rcases lt_or_gt_of_ne hnm with hlt | hlt
    · have hm := blockOffset_monotone d (Nat.succ_le_of_lt hlt)
      rw [blockOffset_succ] at hm
      omega
    · have hn := blockOffset_monotone d (Nat.succ_le_of_lt hlt)
      rw [blockOffset_succ] at hn
      omega

lemma blockEncode_surjective (d : ℕ → ℕ) : Function.Surjective (blockEncode d) := by
  intro k
  have hex : ∃ n, k.val < blockOffset d n := k.property
  have hN : k.val < blockOffset d (Nat.find hex) := Nat.find_spec hex
  have hNzero : Nat.find hex ≠ 0 := by
    intro hz
    simp only [hz, blockOffset_zero] at hN
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hNzero
  have hlo : blockOffset d n ≤ k.val := by
    exact Nat.le_of_not_gt (Nat.find_min hex (by omega : n < Nat.find hex))
  rw [hn, Nat.succ_eq_add_one, blockOffset_succ] at hN
  have hi : k.val - blockOffset d n < d n := by omega
  refine ⟨⟨n, ⟨k.val - blockOffset d n, hi⟩⟩, ?_⟩
  apply Subtype.ext
  change blockOffset d n + (k.val - blockOffset d n) = k.val
  omega

def blockIndexEquiv (d : ℕ → ℕ) : (Σ n, Fin (d n)) ≃ blockIndexSet d :=
  Equiv.ofBijective (blockEncode d) ⟨blockEncode_injective d, blockEncode_surjective d⟩

lemma blockEncode_lt_offset_iff (d : ℕ → ℕ) (i : Σ n, Fin (d n)) (N : ℕ) :
    (blockEncode d i).val < blockOffset d N ↔ i.1 < N := by
  constructor
  · intro h
    by_contra hn
    have hm := blockOffset_monotone d (Nat.le_of_not_gt hn)
    change blockOffset d i.1 + i.2.val < blockOffset d N at h
    omega
  · intro h
    have hm := blockOffset_monotone d (Nat.succ_le_of_lt h)
    rw [blockOffset_succ] at hm
    change blockOffset d i.1 + i.2.val < blockOffset d N
    have hi := i.2.isLt
    omega

end SurveyStatements.P4
