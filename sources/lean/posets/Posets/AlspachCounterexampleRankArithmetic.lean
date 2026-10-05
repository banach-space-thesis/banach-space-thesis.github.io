import Posets.AlspachCounterexampleRankOmega
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Generous countable rank bounds for the threshold-doubling recurrence.
Finite slack is absorbed at the next ω-block; all bounds stay below ω². -/

noncomputable section
open scoped Ordinal
namespace Posets

def alspachRankBound (m n : ℕ) : Ordinal.{0} :=
  ω * (m : Ordinal) + ((4 * (n + 1) : ℕ) : Ordinal)

theorem alspachRankBound_add_omega_add_one (m n : ℕ) :
    alspachRankBound m n + ω + 1 ≤ alspachRankBound (m + 1) n := by
  unfold alspachRankBound
  rw [add_assoc (ω * (m : Ordinal)), Ordinal.natCast_add_omega0]
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  exact add_le_add_left (by exact_mod_cast (show 1 ≤ 4 * (n + 1) by omega)) _

theorem alspachRankBound_add_two (m n : ℕ) :
    alspachRankBound m n + 2 ≤ alspachRankBound m (n + 1) := by
  unfold alspachRankBound
  rw [add_assoc]
  apply add_le_add_left
  exact_mod_cast (show 4 * (n + 1) + 2 ≤ 4 * (n + 1 + 1) by omega)

theorem alspachRankBound_lt_next_block (m n : ℕ) :
    alspachRankBound m n < (ω : Ordinal.{0}) * ((m + 1 : ℕ) : Ordinal) := by
  calc
    alspachRankBound m n < ω * (m : Ordinal) + ω :=
      add_lt_add_left (Ordinal.nat_lt_omega0 (4 * (n + 1))) _
    _ = ω * ((m + 1 : ℕ) : Ordinal) := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]

theorem alspachRankBound_lt_omega_sq (m n : ℕ) :
    alspachRankBound m n < (ω : Ordinal.{0}) ^ (2 : Ordinal) :=
  (alspachRankBound_lt_next_block m n).trans (alspach_finite_ranks_lt m)

theorem alspachRankBound_countable (m n : ℕ) :
    (alspachRankBound m n).card ≤ Cardinal.aleph0 := by
  apply (Ordinal.card_le_card (alspachRankBound_lt_omega_sq m n).le).trans
  simp only [alspach_omega_sq_eq_mul, Ordinal.card_mul, Ordinal.card_omega0,
    Cardinal.aleph0_mul_aleph0, le_refl]

theorem alspach_next_block_add_one_lt_omega_sq (m : ℕ) :
    (ω : Ordinal.{0}) * ((m + 1 : ℕ) : Ordinal) + 1 < ω ^ (2 : Ordinal) := by
  apply lt_trans (b := ω * ((m + 1 + 1 : ℕ) : Ordinal))
  · rw [show ((m + 1 + 1 : ℕ) : Ordinal) = ((m + 1 : ℕ) : Ordinal) + 1 by simp,
      mul_add, mul_one]
    exact add_lt_add_left Ordinal.one_lt_omega0 _
  · exact alspach_finite_ranks_lt (m + 1)

theorem alspach_exists_doubling_depth {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 < (2 : ℝ) ^ m * ε := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1 : ℝ) < 2)
  exact ⟨m, (div_lt_iff₀ hε).mp hm⟩

end Posets
