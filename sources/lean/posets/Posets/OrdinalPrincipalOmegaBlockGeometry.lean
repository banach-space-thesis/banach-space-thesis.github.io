import Posets.OrdinalRegularOmegaBlockModelGeometry

/-! Cofinal block lengths for every infinite additively principal base.
No initial-cardinal or regularity hypothesis is needed for these models. -/

noncomputable section
open Set Order
namespace Posets
universe u

theorem ordinalPrincipalFinitePower_infinite (B : Ordinal.{u})
    (hB : Ordinal.omega0 ≤ B) (a : Ordinal.{u}) (ha : 1 ≤ a) :
    Ordinal.omega0 ≤ B ^ a := by
  have hBp : 0 < B := Ordinal.omega0_pos.trans_le hB
  exact hB.trans (by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right hBp ha)

theorem ordinalPrincipalOmegaBlockMap_length (B : Ordinal.{u})
    (hB : Ordinal.omega0 ≤ B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) (n : ℕ) :
    JLMS.ordinalSpaceBlockLength
      (ordinalOmegaBlockMap B (Ordinal.one_lt_omega0.trans_le hB) h hh h0)
      (ordinalOmegaNatIndexEquiv n) = B ^ (h n : Ordinal) := by
  let hBp := Ordinal.one_lt_omega0.trans_le hB
  have hs := (ordinalOmegaBlockPower_isNormal B hBp h hh h0).strictMono
    (Order.lt_succ (n : Ordinal.{u}))
  rw [← Ordinal.natCast_succ, ordinalOmegaBlockPower_succ B h hh h0] at hs
  have ha := Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_opow_of_principal_add hP (h n : Ordinal)) _ hs
  change ordinalOmegaBlockPower B h (Order.succ (n : Ordinal)) -
    ordinalOmegaBlockPower B h (n : Ordinal) = _
  rw [← Ordinal.natCast_succ, ordinalOmegaBlockPower_succ B h hh h0]
  calc
    _ = (ordinalOmegaBlockPower B h (n : Ordinal) + B ^ (h n : Ordinal)) -
        ordinalOmegaBlockPower B h (n : Ordinal) := by rw [ha]
    _ = _ := Ordinal.add_sub_cancel _ _

theorem ordinalPrincipalOmegaBlockMap_infinite_blocks (B : Ordinal.{u})
    (hB : Ordinal.omega0 ≤ B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (ξ : Iio (Ordinal.omega0 : Ordinal.{u})) :
    Ordinal.omega0 ≤ JLMS.ordinalSpaceBlockLength
      (ordinalOmegaBlockMap B (Ordinal.one_lt_omega0.trans_le hB) h hh h0) ξ := by
  obtain ⟨n, rfl⟩ := ordinalOmegaNatIndexEquiv.surjective ξ
  rw [ordinalPrincipalOmegaBlockMap_length B hB hP h hh h0 n]
  apply ordinalPrincipalFinitePower_infinite B hB
  exact_mod_cast h0.trans (hh.monotone (Nat.zero_le n))

theorem ordinalPrincipalOmegaBlock_head_absorption (B : Ordinal.{u})
    (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (h0 : 1 ≤ h 0) :
    Ordinal.omega0 + B ^ (h 0 : Ordinal) = B ^ (h 0 : Ordinal) := by
  have ht : B ≤ B ^ (h 0 : Ordinal) := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right
      (Ordinal.omega0_pos.trans_le hB.le) (show (1 : Ordinal) ≤ (h 0 : Ordinal) by exact_mod_cast h0)
  exact Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_opow_of_principal_add hP _) _ (hB.trans_le ht)

end Posets
