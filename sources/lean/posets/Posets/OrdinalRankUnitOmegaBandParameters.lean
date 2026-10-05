import Posets.OrdinalRankUnitOmegaOuterFamilies
import Posets.OrdinalRegularOmegaBandParameters

/-! Finite band parameters for powers of the rank-unit base omega^rho. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

theorem ordinal_rank_unit_finite_power_top_level
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) (m : ℕ) (hm : 0 < m) :
    ordinalRankUnitOmegaBase ρ ^ (m : Ordinal) ∈ ordinalTowerLevel
      (ordinalRankUnitOmegaBase ρ ^ (m : Ordinal)) (ρ * (m : Ordinal)) := by
  have hr : ρ * (m : Ordinal) ≠ 0 :=
    mul_ne_zero (Ordinal.omega0_pos.trans_le hρ).ne' (by exact_mod_cast hm.ne')
  rw [ordinalRankUnitOmegaBase, ← Ordinal.opow_mul,
    ordinalTowerLevel, ordinalDerived_Iic_power_self hr]
  exact mem_singleton _

def ordinalRankUnitOmegaBandLevels (ρ : Ordinal.{u}) (N m : ℕ) :
    ℕ → Iic (ρ * (((N+1)*m : ℕ) : Ordinal)) :=
  fun k => ⟨ρ * ((min k N * m : ℕ) : Ordinal), by
    change ρ * ((min k N * m : ℕ) : Ordinal) ≤ ρ * (((N+1)*m : ℕ) : Ordinal)
    apply mul_le_mul_left'
    exact_mod_cast Nat.mul_le_mul_right m ((Nat.min_le_right k N).trans (Nat.le_succ N))⟩

theorem ordinalRankUnitOmegaBandLevels_monotone (ρ : Ordinal.{u}) (N m : ℕ) :
    Monotone (ordinalRankUnitOmegaBandLevels ρ N m) := by
  intro i j hij
  change ρ * ((min i N * m : ℕ) : Ordinal) ≤ ρ * ((min j N * m : ℕ) : Ordinal)
  apply mul_le_mul_left'
  exact_mod_cast Nat.mul_le_mul_right m (min_le_min_right N hij)

theorem ordinalRankUnitOmegaBandLevels_apply_le (ρ : Ordinal.{u}) (N m k : ℕ) (hk : k ≤ N) :
    (ordinalRankUnitOmegaBandLevels ρ N m k).val = ρ * ((k*m : ℕ) : Ordinal) := by
  simp only [ordinalRankUnitOmegaBandLevels, Nat.min_eq_left hk]

theorem ordinalRankUnitOmegaBandLevels_gap (ρ : Ordinal.{u}) (N m k : ℕ) (hk : k < N) :
    (ordinalRankUnitOmegaBandLevels ρ N m k).val + ρ * (m : Ordinal) =
      (ordinalRankUnitOmegaBandLevels ρ N m (k+1)).val := by
  rw [ordinalRankUnitOmegaBandLevels_apply_le ρ N m k hk.le,
    ordinalRankUnitOmegaBandLevels_apply_le ρ N m (k+1) (Nat.succ_le_iff.mpr hk),
    ← mul_add]
  simp only [Nat.add_mul, one_mul, Nat.cast_add]

theorem ordinalRankUnitOmegaBandLevels_upper_lt (ρ : Ordinal.{u})
    (hρ : Ordinal.omega0 ≤ ρ) (N m k : ℕ) (hm : 0 < m) (hk : k < N) :
    (ordinalRankUnitOmegaBandLevels ρ N m (k+1)).val < ρ * (((N+1)*m : ℕ) : Ordinal) := by
  rw [ordinalRankUnitOmegaBandLevels_apply_le ρ N m (k+1) (Nat.succ_le_iff.mpr hk)]
  apply mul_lt_mul_of_pos_left _ (Ordinal.omega0_pos.trans_le hρ)
  exact_mod_cast Nat.mul_lt_mul_of_pos_right (by omega : k + 1 < N + 1) hm

end Posets
