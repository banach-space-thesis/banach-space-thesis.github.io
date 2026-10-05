import Posets.OrdinalRegularOmegaOuterBlocks
import Mathlib.SetTheory.Ordinal.Principal

/-! Actual outer blocks for the first limit power of an arbitrary ordinal
power base.  The rank unit need not be an initial ordinal. -/

noncomputable section
open Set Topology
universe u
namespace Posets

def ordinalRankUnitOmegaBase (ρ : Ordinal.{u}) : Ordinal.{u} := Ordinal.omega0 ^ ρ

theorem ordinalRankUnitOmegaBase_pos (ρ : Ordinal.{u}) :
    0 < ordinalRankUnitOmegaBase ρ := Ordinal.opow_pos _ Ordinal.omega0_pos

theorem ordinalRankUnitOmegaBase_one_lt (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) :
    1 < ordinalRankUnitOmegaBase ρ := by
  have h : (0 : Ordinal.{u}) < ρ := Ordinal.omega0_pos.trans_le hρ
  simpa only [Ordinal.opow_zero] using
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr h

theorem ordinal_rank_unit_finite_power_block_shift
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) {l m : ℕ} (hlm : l < m) :
    (ordinalRankUnitOmegaBase ρ ^ (l : Ordinal) + 1) +
      ordinalRankUnitOmegaBase ρ ^ (m : Ordinal) = ordinalRankUnitOmegaBase ρ ^ (m : Ordinal) := by
  have hB := ordinalRankUnitOmegaBase_one_lt ρ hρ
  have hlt : ordinalRankUnitOmegaBase ρ ^ (l : Ordinal) <
      ordinalRankUnitOmegaBase ρ ^ (m : Ordinal) :=
    (Ordinal.opow_lt_opow_iff_right hB).mpr (by exact_mod_cast hlm)
  have hlim : Order.IsSuccLimit (ordinalRankUnitOmegaBase ρ ^ (m : Ordinal)) :=
    Ordinal.isSuccLimit_opow_left
      (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
        (Ordinal.omega0_pos.trans_le hρ).ne')
      (by exact_mod_cast (by omega : m ≠ 0))
  apply Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_omega0_opow ρ) _)
  simpa only [Ordinal.add_one_eq_succ] using hlim.succ_lt hlt

def ordinalRankUnitOmegaOuterBlock (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ)
    (l m : ℕ) (hlm : l < m) :
    C(Iic (ordinalRankUnitOmegaBase ρ ^ (m : Ordinal)),
      Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) :=
  ordinalOuterBlockMap _ _ _ (ordinal_rank_unit_finite_power_block_shift ρ hρ hlm)
    ((Ordinal.opow_lt_opow_iff_right (ordinalRankUnitOmegaBase_one_lt ρ hρ)).mpr
      (Ordinal.nat_lt_omega0 m))

end Posets
