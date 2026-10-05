import Posets.OrdinalVaryingRankUnits
import Posets.OrdinalClosedCopyInitialPowers

/-! Concrete cofinal varying units at higher initial-base power ranks.
Successor power exponents and limit exponents of cofinality ω give ranks of
cofinality ω, including κ·ω^ω and their further higher analogues. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets

theorem ordinal_higher_limit_rank_principal (κ : Ordinal.{u})
    {η : Ordinal.{u}} (hη : η ≠ 0) :
    Ordinal.Principal (· + ·) (κ * Ordinal.omega0 ^ η) := by
  apply Ordinal.principal_add_mul_of_principal_add κ
    ((Ordinal.one_lt_of_isSuccLimit
      (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hη)).ne')
    (Ordinal.principal_add_omega0_opow η)

theorem ordinal_higher_limit_rank_cof_succ {κ : Ordinal.{u}} (hκ : 0 < κ)
    (η : Ordinal.{u}) :
    (κ * Ordinal.omega0 ^ Order.succ η).cof = Cardinal.aleph0 := by
  rw [Ordinal.opow_succ, ← mul_assoc]
  exact ((Ordinal.isNormal_mul_right
    (mul_pos hκ (Ordinal.opow_pos η Ordinal.omega0_pos))).cof_eq
      Ordinal.isSuccLimit_omega0).trans Ordinal.cof_omega0

theorem ordinal_higher_limit_rank_cof_limit {κ : Ordinal.{u}} (hκ : 0 < κ)
    {η : Ordinal.{u}} (hη : IsSuccLimit η) (hcf : η.cof = Cardinal.aleph0) :
    (κ * Ordinal.omega0 ^ η).cof = Cardinal.aleph0 := by
  exact ((Ordinal.isNormal_mul_right hκ).cof_eq
    (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hη.ne_bot)).trans
      (((Ordinal.isNormal_opow Ordinal.one_lt_omega0).cof_eq hη).trans hcf)

theorem exists_initialPowerVaryingRankUnits_succ
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (η : Ordinal.{u}) (s : ℕ → ℕ) :
    Nonempty (OrdinalVaryingRankUnits (c.ord * Ordinal.omega0 ^ Order.succ η) s) := by
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)
  have hωκ : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hc
  exact exists_ordinalVaryingRankUnits _
    (ordinal_higher_limit_rank_principal c.ord (Order.succ_ne_bot η))
    (hωκ.trans_le (Ordinal.le_mul_left _ (Ordinal.opow_pos _ Ordinal.omega0_pos)))
    (ordinal_higher_limit_rank_cof_succ hκ η) s

theorem exists_initialPowerVaryingRankUnits_limit
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    {η : Ordinal.{u}} (hη : IsSuccLimit η) (hcf : η.cof = Cardinal.aleph0)
    (s : ℕ → ℕ) :
    Nonempty (OrdinalVaryingRankUnits (c.ord * Ordinal.omega0 ^ η) s) := by
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)
  have hωκ : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hc
  exact exists_ordinalVaryingRankUnits _
    (ordinal_higher_limit_rank_principal c.ord hη.ne_bot)
    (hωκ.trans_le (Ordinal.le_mul_left _ (Ordinal.opow_pos _ Ordinal.omega0_pos)))
    (ordinal_higher_limit_rank_cof_limit hκ hη hcf) s

theorem exists_initialPowerVaryingRankUnits_omega
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c) (s : ℕ → ℕ) :
    Nonempty (OrdinalVaryingRankUnits (c.ord * Ordinal.omega0 ^ Ordinal.omega0) s) :=
  exists_initialPowerVaryingRankUnits_limit c hc Ordinal.isSuccLimit_omega0 Ordinal.cof_omega0 s

end Posets
