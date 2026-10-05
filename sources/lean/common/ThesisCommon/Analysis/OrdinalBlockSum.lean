import ThesisCommon.Analysis.OrdinalIntervalSum

/-! Countable concatenation of nonempty compact ordinal blocks. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

def ordinalBlockStart (a : ℕ → Ordinal.{u}) : ℕ → Ordinal.{u}
  | 0 => 0
  | n + 1 => ordinalBlockStart a n + a n + 1

@[simp] theorem ordinalBlockStart_zero (a : ℕ → Ordinal.{u}) : ordinalBlockStart a 0 = 0 := rfl
@[simp] theorem ordinalBlockStart_succ (a : ℕ → Ordinal.{u}) (n : ℕ) :
    ordinalBlockStart a (n + 1) = ordinalBlockStart a n + a n + 1 := rfl

def ordinalBlockSup (a : ℕ → Ordinal.{u}) : Ordinal.{u} := ⨆ n, ordinalBlockStart a n

theorem ordinalBlockStart_strictMono (a : ℕ → Ordinal.{u}) : StrictMono (ordinalBlockStart a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [ordinalBlockStart_succ, Ordinal.add_one_eq_succ]
  exact (Ordinal.le_add_right _ _).trans_lt (lt_succ _)

theorem ordinalBlockStart_le_sup (a : ℕ → Ordinal.{u}) (n : ℕ) :
    ordinalBlockStart a n ≤ ordinalBlockSup a :=
  le_ciSup (Ordinal.bddAbove_range _) n

theorem ordinalBlockStart_lt_sup (a : ℕ → Ordinal.{u}) (n : ℕ) :
    ordinalBlockStart a n < ordinalBlockSup a :=
  (ordinalBlockStart_strictMono a (Nat.lt_succ_self n)).trans_le (ordinalBlockStart_le_sup a (n + 1))

theorem ordinalBlockEnd_lt_sup (a : ℕ → Ordinal.{u}) (n : ℕ) :
    ordinalBlockStart a n + a n < ordinalBlockSup a := by
  have h : ordinalBlockStart a n + a n < ordinalBlockStart a (n + 1) := by
    rw [ordinalBlockStart_succ, Ordinal.add_one_eq_succ]
    exact lt_succ _
  exact h.trans_le (ordinalBlockStart_le_sup a (n + 1))

theorem ordinalBlockEnd_lt_start {a : ℕ → Ordinal.{u}} {n m : ℕ} (hnm : n < m) :
    ordinalBlockStart a n + a n < ordinalBlockStart a m := by
  have h : ordinalBlockStart a n + a n < ordinalBlockStart a (n + 1) := by
    rw [ordinalBlockStart_succ, Ordinal.add_one_eq_succ]
    exact lt_succ _
  exact h.trans_le ((ordinalBlockStart_strictMono a).monotone (Nat.succ_le_of_lt hnm))

theorem ordinalBlockStart_zero_or_succ (a : ℕ → Ordinal.{u}) (n : ℕ) :
    ordinalBlockStart a n = 0 ∨ ∃ β, ordinalBlockStart a n = succ β := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n => exact Or.inr ⟨ordinalBlockStart a n + a n, Ordinal.add_one_eq_succ _⟩

theorem ordinalBlock_covers {a : ℕ → Ordinal.{u}} {x : Ordinal.{u}}
    (hx : x < ordinalBlockSup a) :
    ∃ n, ordinalBlockStart a n ≤ x ∧ x ≤ ordinalBlockStart a n + a n := by
  have hex : ∃ n, x < ordinalBlockStart a n := by
    by_contra! h
    exact hx.not_ge (ciSup_le h)
  have hzero : Nat.find hex ≠ 0 := by
    intro h
    have hspec := Nat.find_spec hex
    rw [h, ordinalBlockStart_zero] at hspec
    exact (not_lt_of_ge (show (0 : Ordinal.{u}) ≤ x from bot_le)) hspec
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hprev := Nat.find_min hex (show n < Nat.find hex by omega)
  have hnext := Nat.find_spec hex
  rw [hn, ordinalBlockStart_succ, Ordinal.add_one_eq_succ] at hnext
  exact ⟨n, le_of_not_gt hprev, lt_succ_iff.mp hnext⟩

end ThesisCommon
