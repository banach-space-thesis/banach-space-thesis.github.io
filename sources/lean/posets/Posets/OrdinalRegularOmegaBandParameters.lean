import Posets.OrdinalRegularOmegaOuterFamilies
import Posets.OrdinalClosedCopyInitialPowers
import ThesisCommon.Analysis.OrdinalBakerPowers

/-! Concrete ranks and finite ancestor-band levels for the regular-cardinal
construction. The initial-ordinal power identity also holds for singular
uncountable cardinals; regularity is used later in the cell extraction. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

theorem ordinalTower_top_mem_subtypeDerived {θ γ : Ordinal.{u}}
    (hθ : θ ∈ ordinalTowerLevel θ γ) :
    (⟨θ, show θ ≤ θ from le_rfl⟩ : Iic θ) ∈ ordinalDerived (univ : Set (Iic θ)) γ := by
  have he := ordinalDerived_image_closedEmbedding
    (isClosed_Iic : IsClosed (Iic θ)).isClosedEmbedding_subtypeVal univ γ
  rw [image_univ, Subtype.range_coe] at he
  change θ ∈ ordinalDerived (Iic θ) γ at hθ
  rw [he] at hθ
  obtain ⟨x, hx, heq⟩ := hθ
  have hxθ : x = (⟨θ, show θ ≤ θ from le_rfl⟩ : Iic θ) := Subtype.ext heq
  simpa only [hxθ] using hx

theorem ordinal_initial_finite_power_top_level
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c) (m : ℕ) (hm : 0 < m) :
    c.ord ^ (m : Ordinal) ∈ ordinalTowerLevel (c.ord ^ (m : Ordinal)) (c.ord * (m : Ordinal)) := by
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)
  have hρ : c.ord * (m : Ordinal) ≠ 0 := mul_ne_zero hκ.ne' (by exact_mod_cast hm.ne')
  rw [← ordinal_uncountable_initial_power_rank hc (m : Ordinal),
    ordinalTowerLevel, ordinalDerived_Iic_power_self hρ]
  exact mem_singleton _

def ordinalRegularOmegaBandLevels (c : Cardinal.{u}) (N m : ℕ) :
    ℕ → Iic (c.ord * (((N+1)*m : ℕ) : Ordinal)) :=
  fun k => ⟨c.ord * ((min k N * m : ℕ) : Ordinal), by
    change c.ord * ((min k N * m : ℕ) : Ordinal) ≤ c.ord * (((N+1)*m : ℕ) : Ordinal)
    apply mul_le_mul_left'
    exact_mod_cast Nat.mul_le_mul_right m ((Nat.min_le_right k N).trans (Nat.le_succ N))⟩

theorem ordinalRegularOmegaBandLevels_monotone (c : Cardinal.{u}) (N m : ℕ) :
    Monotone (ordinalRegularOmegaBandLevels c N m) := by
  intro i j hij
  change c.ord * ((min i N * m : ℕ) : Ordinal) ≤ c.ord * ((min j N * m : ℕ) : Ordinal)
  apply mul_le_mul_left'
  exact_mod_cast Nat.mul_le_mul_right m (min_le_min_right N hij)

theorem ordinalRegularOmegaBandLevels_apply_le (c : Cardinal.{u}) (N m k : ℕ) (hk : k ≤ N) :
    (ordinalRegularOmegaBandLevels c N m k).val = c.ord * ((k*m : ℕ) : Ordinal) := by
  simp only [ordinalRegularOmegaBandLevels, Nat.min_eq_left hk]

theorem ordinalRegularOmegaBandLevels_gap (c : Cardinal.{u}) (N m k : ℕ) (hk : k < N) :
    (ordinalRegularOmegaBandLevels c N m k).val + c.ord * (m : Ordinal) =
      (ordinalRegularOmegaBandLevels c N m (k+1)).val := by
  rw [ordinalRegularOmegaBandLevels_apply_le c N m k hk.le,
    ordinalRegularOmegaBandLevels_apply_le c N m (k+1) (Nat.succ_le_iff.mpr hk),
    ← mul_add]
  simp only [Nat.add_mul, one_mul, Nat.cast_add]

theorem ordinalRegularOmegaBandLevels_upper_lt (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (N m k : ℕ) (hm : 0 < m) (hk : k < N) :
    (ordinalRegularOmegaBandLevels c N m (k+1)).val < c.ord * (((N+1)*m : ℕ) : Ordinal) := by
  rw [ordinalRegularOmegaBandLevels_apply_le c N m (k+1) (Nat.succ_le_iff.mpr hk)]
  apply mul_lt_mul_of_pos_left _ (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc))
  exact_mod_cast Nat.mul_lt_mul_of_pos_right (by omega : k + 1 < N + 1) hm

end Posets
