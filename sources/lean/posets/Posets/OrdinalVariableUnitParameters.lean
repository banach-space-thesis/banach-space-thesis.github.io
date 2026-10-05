import Posets.OrdinalRankUnitOmegaBandParameters

/-! The concrete cofinal rank data for varying-unit finite band selection.
These are ordinal arithmetic conditions; no operator factors are inputs. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

structure OrdinalVariableUnitParameters (γ : Ordinal.{u}) (N : ℕ) where
  unit : ℕ → Iio γ
  unit_large : ∀ n, Ordinal.omega0 ≤ (unit n).val
  sourceStrictMono : StrictMono (fun n => (unit n).val * (((N+1)*2 : ℕ) : Ordinal))
  source_lt : ∀ n, (unit n).val * (((N+1)*2 : ℕ) : Ordinal) < γ
  cofinal : ∀ β < γ, ∃ n, β < (unit n).val

namespace OrdinalVariableUnitParameters
variable {γ : Ordinal.{u}} {N : ℕ} (P : OrdinalVariableUnitParameters γ N)

def outerRank (n : ℕ) : Ordinal.{u} := (P.unit n).val * (((N+1)*2 : ℕ) : Ordinal)

theorem outerRank_pos (n : ℕ) : 0 < P.outerRank n := by
  apply mul_pos (Ordinal.omega0_pos.trans_le (P.unit_large n))
  exact_mod_cast (Nat.mul_pos (Nat.succ_pos N) (by omega : 0 < 2))

theorem unit_le_outerRank (n : ℕ) : (P.unit n).val ≤ P.outerRank n := by
  apply Ordinal.le_mul_left
  exact_mod_cast (Nat.mul_pos (Nat.succ_pos N) (by omega : 0 < 2))

theorem outerRank_cofinal : ∀ β < γ, ∃ n, β < P.outerRank n := by
  intro β hβ
  obtain ⟨n, hn⟩ := P.cofinal β hβ
  exact ⟨n, hn.trans_le (P.unit_le_outerRank n)⟩

theorem unit_strictMono : StrictMono (fun n => (P.unit n).val) := by
  intro i j hij
  apply lt_of_not_ge
  intro hji
  exact (P.sourceStrictMono hij).not_ge (mul_le_mul_right' hji (((N+1)*2 : ℕ) : Ordinal))

def sourceUnit (n : ℕ) : Ordinal.{u} := (P.unit (n+1)).val
def sourceRank (n : ℕ) : Ordinal.{u} := P.outerRank (n+1)
def source (n : ℕ) : Ordinal.{u} := Ordinal.omega0 ^ P.sourceRank n

theorem source_eq_rank_unit_power (n : ℕ) :
    P.source n = ordinalRankUnitOmegaBase (P.sourceUnit n) ^ (((N+1)*2 : ℕ) : Ordinal) :=
  Ordinal.opow_mul _ _ _

theorem source_top_level (n : ℕ) : P.source n ∈ ordinalTowerLevel (P.source n) (P.sourceRank n) := by
  have hrank : P.sourceRank n ≠ 0 := (P.outerRank_pos (n+1)).ne'
  rw [source, ordinalTowerLevel, ordinalDerived_Iic_power_self hrank]
  exact mem_singleton _

theorem sourceUnit_strictMono : StrictMono P.sourceUnit :=
  fun _ _ h => P.unit_strictMono (Nat.add_lt_add_right h 1)

theorem sourceUnit_subsequence_cofinal (k : ℕ → ℕ) (hk : StrictMono k) :
    ∀ β < γ, ∃ n, β < P.sourceUnit (k n) := by
  intro β hβ
  obtain ⟨n, hn⟩ := P.cofinal β hβ
  exact ⟨n, hn.trans_le (P.unit_strictMono.monotone ((hk.id_le n).trans (Nat.le_succ _)))⟩

theorem power_sourceUnit_subsequence_cofinal (hγ : Order.IsSuccLimit γ)
    (k : ℕ → ℕ) (hk : StrictMono k) :
    ∀ β < Ordinal.omega0 ^ γ, ∃ n, β < Ordinal.omega0 ^ P.sourceUnit (k n) := by
  intro β hβ
  obtain ⟨α, hαγ, hβα⟩ :=
    (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hγ).mp hβ
  obtain ⟨n, hn⟩ := P.sourceUnit_subsequence_cofinal k hk α hαγ
  exact ⟨n, hβα.trans ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hn)⟩

end OrdinalVariableUnitParameters
end Posets
