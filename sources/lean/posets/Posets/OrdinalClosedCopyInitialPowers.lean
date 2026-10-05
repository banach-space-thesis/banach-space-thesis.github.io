import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Regular

/-! Cantor--Bendixson exponents of finite powers of an uncountable initial
ordinal.  No regularity assumption is needed for these arithmetic identities. -/

noncomputable section
universe u
namespace Posets

theorem ordinal_uncountable_initial_omega_power {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) : Ordinal.omega0 ^ c.ord = c.ord := by
  apply le_antisymm
  · apply (Ordinal.opow_le_of_isSuccLimit Ordinal.omega0_ne_zero
      (Cardinal.isSuccLimit_ord hc.le)).mpr
    intro a ha
    apply (Cardinal.lt_ord.mpr ?_).le
    by_cases ha0 : a = 0
    · simp only [ha0, Ordinal.opow_zero, Ordinal.card_one]
      exact (Cardinal.nat_lt_aleph0 1).trans hc
    · rw [Ordinal.card_omega0_opow ha0]
      exact max_lt hc (Cardinal.lt_ord.mp ha)
  · exact Ordinal.right_le_opow _ Ordinal.one_lt_omega0

theorem ordinal_uncountable_initial_power_rank {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) (a : Ordinal.{u}) :
    Ordinal.omega0 ^ (c.ord * a) = c.ord ^ a := by
  rw [Ordinal.opow_mul, ordinal_uncountable_initial_omega_power hc]

end Posets
