import Mathlib.SetTheory.Ordinal.NaturalOps
import Mathlib.SetTheory.Ordinal.Exponential

/-! Natural-sum closure at the two ordinal bounds used in Section 3. -/

universe u
noncomputable section
open Ordinal Order
open scoped Ordinal NaturalOps
namespace Posets

theorem nadd_lt_omega0 {a b : Ordinal.{u}} (ha : a < ω) (hb : b < ω) :
    a ♯ b < ω := by
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp ha
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hb
  simpa only [Ordinal.nadd_nat, ← Nat.cast_add] using Ordinal.nat_lt_omega0 (m + n)

private theorem nadd_omega_block_bound (m n : ℕ)
    (ih : ∀ k < m, (ω * (k : Ordinal.{u})) ♯ (ω * (n : Ordinal.{u})) ≤ ω * ((k + n : ℕ) : Ordinal.{u}))
    {a : Ordinal.{u}} (ha : a < ω * (m : Ordinal.{u})) :
    a ♯ (ω * (n : Ordinal.{u})) < ω * ((m + n : ℕ) : Ordinal.{u}) := by
  have hdiv : a / ω < (m : Ordinal.{u}) := (Ordinal.div_lt Ordinal.omega0_ne_zero).mpr ha
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (hdiv.trans (Ordinal.nat_lt_omega0 m))
  obtain ⟨r, hr⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt a Ordinal.omega0_ne_zero)
  have hkm : k < m := by rw [hk] at hdiv; exact_mod_cast hdiv
  have hae : a = ω * (k : Ordinal.{u}) + (r : Ordinal.{u}) := by
    simpa only [hk, hr] using (Ordinal.div_add_mod a ω).symm
  calc
    a ♯ (ω * (n : Ordinal.{u})) = ((ω * (k : Ordinal.{u})) ♯ (ω * (n : Ordinal.{u}))) + r := by
      rw [hae, ← Ordinal.nadd_nat, Ordinal.nadd_right_comm, Ordinal.nadd_nat]
    _ ≤ ω * ((k + n : ℕ) : Ordinal.{u}) + r := add_le_add_right (ih k hkm) _
    _ < ω * ((k + n : ℕ) : Ordinal.{u}) + ω :=
      (add_lt_add_iff_left _).mpr (Ordinal.nat_lt_omega0 r)
    _ = ω * ((k + n + 1 : ℕ) : Ordinal.{u}) := by
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    _ ≤ ω * ((m + n : ℕ) : Ordinal.{u}) := mul_le_mul_left' (by exact_mod_cast (show k + n + 1 ≤ m + n by omega)) _

theorem nadd_omega_mul_nat_le (m n : ℕ) :
    (ω * (m : Ordinal.{u})) ♯ (ω * (n : Ordinal.{u})) ≤ ω * ((m + n : ℕ) : Ordinal.{u}) := by
  apply Ordinal.nadd_le_iff.mpr
  constructor
  · intro a ha
    exact nadd_omega_block_bound m n (fun k hk => nadd_omega_mul_nat_le k n) ha
  · intro b hb
    rw [Ordinal.nadd_comm, Nat.add_comm m n]
    exact nadd_omega_block_bound n m (fun k hk => nadd_omega_mul_nat_le k m) hb
termination_by m + n
decreasing_by all_goals omega

theorem nadd_lt_omega0_sq {a b : Ordinal.{u}} (ha : a < ω ^ (2 : Ordinal.{u}))
    (hb : b < ω ^ (2 : Ordinal.{u})) : a ♯ b < ω ^ (2 : Ordinal.{u}) := by
  have hae : a < ω ^ Order.succ (1 : Ordinal.{u}) := by simpa only [Ordinal.succ_one] using ha
  have hbe : b < ω ^ Order.succ (1 : Ordinal.{u}) := by simpa only [Ordinal.succ_one] using hb
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0_opow_succ.mp hae
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0_opow_succ.mp hbe
  simp only [Ordinal.opow_one] at hm hn
  exact (Ordinal.nadd_lt_nadd hm hn).trans_le
    ((nadd_omega_mul_nat_le m n).trans
      (by simpa only [Ordinal.opow_one] using
        (Ordinal.omega0_opow_mul_nat_lt (show (1 : Ordinal.{u}) < 2 by norm_num) (m + n)).le))

end Posets
