import Posets.OrdinalCofinalBandReadback
import Mathlib.SetTheory.Ordinal.Principal

/-! A countably cofinal limit power has cofinal target ranks whose every
finite padding still lies below the original rank. These are actual ordinal
sequences; no Banach-space preservation hypothesis is introduced. -/
noncomputable section
namespace Posets
open Set Ordinal Order
universe u
set_option maxHeartbeats 800000

theorem ordinal_power_cofinal_exists_finitely_padded_ranks
    (δ : Ordinal.{u}) (hδ : 1 < δ)
    (hcof : (Ordinal.omega0 ^ δ).cof = Cardinal.aleph0) :
    ∃ b : ℕ → Ordinal.{u}, StrictMono b ∧
      (∀ n, b n ≠ 0 ∧ 1 + b n = b n) ∧
      (∀ n m : ℕ, b n * (m : Ordinal) < Ordinal.omega0 ^ δ) ∧
      ∀ β < Ordinal.omega0 ^ δ, ∃ n, β < b n := by
  obtain ⟨a, ha, hc⟩ := ordinal_cof_aleph0_exists_strictMono_cofinal _ hcof
  obtain ⟨N, hN⟩ := hc Ordinal.omega0 (Ordinal.left_lt_opow Ordinal.one_lt_omega0 hδ)
  let b : ℕ → Ordinal.{u} := fun n => (a (n+N)).val
  have hω (n : ℕ) : Ordinal.omega0 ≤ b n :=
    hN.le.trans (ha.monotone (Nat.le_add_left N n))
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    exact ha (Nat.add_lt_add_right hnm N)
  · intro n
    exact ⟨(Ordinal.omega0_pos.trans_le (hω n)).ne', Ordinal.one_add_of_omega0_le (hω n)⟩
  · intro n m
    exact Ordinal.mul_lt_omega0_opow (lt_trans zero_lt_one hδ)
      (a (n+N)).property (Ordinal.nat_lt_omega0 m)
  · intro β hβ
    obtain ⟨n, hn⟩ := hc β hβ
    exact ⟨n, hn.trans_le (ha.monotone (Nat.le_add_right n N))⟩

theorem ordinal_cofinal_exists_finitely_padded_ranks
    (δ : Ordinal.{u}) (hδ : δ.cof = Cardinal.aleph0) :
    ∃ b : ℕ → Ordinal.{u}, StrictMono b ∧
      (∀ n, b n ≠ 0 ∧ 1 + b n = b n) ∧
      (∀ n m : ℕ, b n * (m : Ordinal) < Ordinal.omega0 ^ δ) ∧
      ∀ β < Ordinal.omega0 ^ δ, ∃ n, β < b n := by
  obtain ⟨a, ha, hc⟩ := ordinal_cof_aleph0_exists_strictMono_cofinal δ hδ
  have hd : IsSuccLimit δ := Ordinal.aleph0_le_cof.mp hδ.ge
  let b : ℕ → Ordinal.{u} := fun n => Ordinal.omega0 ^ (a (n+1)).val
  have hapos (n : ℕ) : 0 < (a (n+1)).val :=
    (Ordinal.zero_le (a n).val).trans_lt (ha (Nat.lt_succ_self n))
  have hbbelow (n : ℕ) : b n < Ordinal.omega0 ^ δ :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (a (n+1)).property
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      (ha (Nat.add_lt_add_right hnm 1))
  · intro n
    refine ⟨Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero, ?_⟩
    apply Ordinal.add_omega0_opow
    simpa only [Ordinal.opow_zero] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hapos n)
  · intro n m
    exact Ordinal.mul_lt_omega0_opow hd.bot_lt (hbbelow n) (Ordinal.nat_lt_omega0 m)
  · intro β hβ
    obtain ⟨ξ, hξ, hβξ⟩ :=
      (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hd).mp hβ
    obtain ⟨n, hn⟩ := hc ξ hξ
    refine ⟨n, hβξ.trans ?_⟩
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      (hn.trans (ha (Nat.lt_succ_self n)))

end Posets
