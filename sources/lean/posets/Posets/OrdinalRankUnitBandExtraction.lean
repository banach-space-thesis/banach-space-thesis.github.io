import Posets.OrdinalClosedCopyUniformUpperFiber
import Posets.OrdinalClosedCopySeparatedGeometry

/-! Finite coefficient loss at an arbitrary ordinal rank unit.  For a base
ω^ρ, the construction spends one copy of ρ, rather than an ordinary successor
rank.  The estimate therefore remains strict at higher limit exponents. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinal_packet_threshold_lt {B δ : Ordinal.{u}}
    (hB : 2 < B) (hδ : 0 < δ) (m : ℕ) :
    δ * Order.succ (B ^ (m : Ordinal)) < δ * (B * B ^ (m : Ordinal)) := by
  have htwo : (0 : Ordinal.{u}) < 2 := by exact_mod_cast (by omega : (0 : ℕ) < 2)
  have hB0 : 0 < B := htwo.trans hB
  have hp : 0 < B ^ (m : Ordinal) := Ordinal.opow_pos _ hB0
  have hle : δ ≤ δ * B ^ (m : Ordinal) := Ordinal.le_mul_left δ hp
  have he : B * B ^ (m : Ordinal) = B ^ (m : Ordinal) * B := by
    rw [← Ordinal.opow_one_add, Ordinal.one_add_natCast]
    exact Ordinal.opow_succ _ _
  calc
    δ * Order.succ (B ^ (m : Ordinal)) = δ * B ^ (m : Ordinal) + δ := Ordinal.mul_succ _ _
    _ ≤ δ * B ^ (m : Ordinal) + δ * B ^ (m : Ordinal) := add_le_add_left hle _
    _ = (δ * B ^ (m : Ordinal)) * 2 := by
      rw [← Ordinal.succ_one, Ordinal.mul_succ, mul_one]
    _ < (δ * B ^ (m : Ordinal)) * B := mul_lt_mul_of_pos_left hB (mul_pos hδ hp)
    _ = δ * (B * B ^ (m : Ordinal)) := by rw [he, mul_assoc]

theorem ordinalRankUnit_exists_band_geometry
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ)
    (N m k : ℕ) (hm : 2 ≤ m) (hk : k < N)
    (F : Set Ordinal.{u}) (hF : IsCompact F)
    (hFθ : F ⊆ Iic ((Ordinal.omega0 ^ ρ) ^ (((N+1)*m : ℕ) : Ordinal)))
    (hrank : (ordinalDerived F (ρ * (((N+1)*m : ℕ) : Ordinal))).Nonempty) :
    Nonempty (OrdinalSeparatedBandCoreGeometry F
      ((Ordinal.omega0 ^ ρ) ^ (((N+1)*m : ℕ) : Ordinal))
      (ρ * (((k+1)*m : ℕ) : Ordinal))
      (ρ * ((k*m : ℕ) : Ordinal)) (ρ * ((m-1 : ℕ) : Ordinal))) := by
  let B := Ordinal.omega0 ^ ρ
  let t : ℕ := (N+1)*m
  let u : ℕ := (k+1)*m
  let v : ℕ := (N-k)*m
  have hρpos : 0 < ρ := Ordinal.omega0_pos.trans_le hρ
  have hBω : Ordinal.omega0 ≤ B := hρ.trans (Ordinal.right_le_opow ρ Ordinal.one_lt_omega0)
  have hB2 : 2 < B := (Ordinal.nat_lt_omega0 2).trans_le hBω
  have hBpos : 0 < B := Ordinal.omega0_pos.trans_le hBω
  have hscale (j : ℕ) : Ordinal.omega0 ^ (ρ * (j : Ordinal)) = B ^ (j : Ordinal) :=
    Ordinal.opow_mul _ _ _
  have hm0 : 0 < m := by omega
  have hu2 : 2 ≤ u := by
    dsimp only [u]
    exact hm.trans (Nat.le_mul_of_pos_left m (Nat.succ_pos k))
  have ht0 : 0 < t := Nat.mul_pos (Nat.succ_pos N) hm0
  have huv : u + v = t := by
    dsimp only [u, v, t]
    rw [← Nat.add_mul]
    congr 1
    omega
  have hranks : ρ * ((k*m : ℕ) : Ordinal) + ρ * ((m-1 : ℕ) : Ordinal) =
      ρ * ((u-1 : ℕ) : Ordinal) := by
    rw [← mul_add, ← Nat.cast_add]
    congr 1
    congr 1
    dsimp only [u]
    rw [Nat.add_mul, one_mul]
    omega
  have hupper : ρ * (u : Ordinal) ≠ 0 :=
    mul_ne_zero hρpos.ne' (by exact_mod_cast (show u ≠ 0 by omega))
  have hretained : ρ * ((u-1 : ℕ) : Ordinal) ≠ 0 :=
    mul_ne_zero hρpos.ne' (by exact_mod_cast (show u-1 ≠ 0 by omega))
  have hsource : ρ * (t : Ordinal) ≠ 0 :=
    mul_ne_zero hρpos.ne' (by exact_mod_cast ht0.ne')
  have hθtop : B ^ (t : Ordinal) ∈ ordinalTowerLevel (B ^ (t : Ordinal)) (ρ * (t : Ordinal)) := by
    rw [← hscale t, ordinalTowerLevel, ordinalDerived_Iic_power_self hsource]
    exact mem_singleton _
  have hθlevel : B ^ (t : Ordinal) ∈ ordinalTowerLevel (B ^ (t : Ordinal)) (ρ * (u : Ordinal)) := by
    apply ordinalTowerLevel_antitone _ _ hθtop
    exact mul_le_mul_left' (by exact_mod_cast Nat.le.intro huv) ρ
  have hθeq : B ^ (u : Ordinal) * B ^ (v : Ordinal) = B ^ (t : Ordinal) := by
    rw [← Ordinal.opow_add, ← Nat.cast_add, huv]
  have hne : F.Nonempty := by
    have h := hrank.mono (ordinalDerived_antitone hF.isClosed (Ordinal.zero_le (ρ * (t : Ordinal))))
    simpa only [ordinalDerived_zero] using h
  obtain ⟨η, e, he, _⟩ := ordinal_compact_order_homeomorph hF hne
  have hη : B ^ (t : Ordinal) ≤ η := by
    simpa only [hscale] using ordinal_power_le_compact_model e hsource hrank
  have hfull : Ordinal.lift.{u+1} (B ^ (t : Ordinal)) ≤
      Ordinal.type (· < · : F → _ → Prop) := by
    rw [ordinal_type_compact_order_model e he]
    exact Ordinal.lift_le.mpr (hη.trans (Order.le_succ η))
  have hlarge : Ordinal.lift.{u+1}
      (Ordinal.omega0 ^ (ρ * ((u-1 : ℕ) : Ordinal)) * Order.succ (B ^ (v : Ordinal))) <
      Ordinal.type (· < · : F → _ → Prop) := by
    rw [hscale]
    apply (Ordinal.lift_lt.mpr ?_).trans_le hfull
    have ht := ordinal_packet_threshold_lt hB2 (Ordinal.opow_pos ((u-1 : ℕ) : Ordinal) hBpos) v
    have he : B ^ ((u-1 : ℕ) : Ordinal) * B = B ^ (u : Ordinal) := by
      have huone : ((u-1 : ℕ) : Ordinal.{u}) + 1 = (u : Ordinal) := by
        exact_mod_cast Nat.sub_add_cancel (show 1 ≤ u by omega)
      rw [← Ordinal.opow_succ, ← Ordinal.add_one_eq_succ, huone]
    simpa only [← mul_assoc, he, hθeq] using ht
  obtain ⟨y, hyo, hyrank⟩ := ordinalTower_exists_high_upper_cell_uniform
    hupper hretained hθlevel (β := B ^ (v : Ordinal))
    (by rw [hscale, hθeq]) hF hFθ hlarge
  have hb : ρ * ((m-1 : ℕ) : Ordinal) ≠ 0 :=
    mul_ne_zero hρpos.ne' (by exact_mod_cast (show m-1 ≠ 0 by omega))
  have habs : 1 + ρ * ((m-1 : ℕ) : Ordinal) = ρ * ((m-1 : ℕ) : Ordinal) :=
    Ordinal.one_add_of_omega0_le (hρ.trans
      (Ordinal.le_mul_left ρ (by exact_mod_cast (show 0 < m-1 by omega))))
  apply ordinalSeparatedBandCoreGeometry_of_isolated_upper_cell hθlevel y hyo hF hFθ hb habs
  · rw [hranks]
    exact mul_le_mul_left' (by exact_mod_cast Nat.sub_le u 1) ρ
  · rwa [hranks]

end Posets
