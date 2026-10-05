import Posets.OrdinalRegularOmegaBandParameters
import Posets.OrdinalClosedCopyHeightLoss
import Posets.OrdinalClosedCopySeparatedGeometry

/-! Concrete upper-band extraction for every uncountable initial ordinal.
A single finite exponent is spent on the uniform fiber bound; the lower
coordinate still contains the interval of height m-1. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalInitialOmega_exists_band_geometry_height_loss
    {c : Cardinal.{u}} (hu : Cardinal.aleph0 < c)
    (N m k : ℕ) (hm : 2 ≤ m) (hk : k < N)
    (F : Set Ordinal.{u}) (hF : IsCompact F)
    (hFθ : F ⊆ Iic (c.ord ^ (((N+1)*m : ℕ) : Ordinal)))
    (hrank : (ordinalDerived F (c.ord * (((N+1)*m : ℕ) : Ordinal))).Nonempty) :
    Nonempty (OrdinalSeparatedBandCoreGeometry F (c.ord ^ (((N+1)*m : ℕ) : Ordinal))
      (c.ord * (((k+1)*m : ℕ) : Ordinal))
      (c.ord * ((k*m : ℕ) : Ordinal)) (c.ord * ((m-1 : ℕ) : Ordinal))) := by
  let t : ℕ := (N+1)*m
  let u : ℕ := (k+1)*m
  let v : ℕ := (N-k)*m
  have hm0 : 0 < m := by omega
  have hu2 : 2 ≤ u := by
    dsimp only [u]
    exact hm.trans (Nat.le_mul_of_pos_left m (Nat.succ_pos k))
  have hv0 : 0 < v := Nat.mul_pos (Nat.sub_pos_of_lt hk) hm0
  have ht0 : 0 < t := Nat.mul_pos (Nat.succ_pos N) hm0
  have huv : u + v = t := by
    dsimp only [u, v, t]
    rw [← Nat.add_mul]
    congr 1
    omega
  have hranks : c.ord * ((k*m : ℕ) : Ordinal) + c.ord * ((m-1 : ℕ) : Ordinal) =
      c.ord * ((u-1 : ℕ) : Ordinal) := by
    rw [← mul_add, ← Nat.cast_add]
    congr 1
    congr 1
    dsimp only [u]
    rw [Nat.add_mul, one_mul]
    omega
  have hpos : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hu.le)
  have hupper : c.ord * (u : Ordinal) ≠ 0 :=
    mul_ne_zero hpos.ne' (by exact_mod_cast (show u ≠ 0 by omega))
  have hretained : c.ord * ((u-1 : ℕ) : Ordinal) ≠ 0 :=
    mul_ne_zero hpos.ne' (by exact_mod_cast (show u-1 ≠ 0 by omega))
  have hθlevel : c.ord ^ (t : Ordinal) ∈
      ordinalTowerLevel (c.ord ^ (t : Ordinal)) (c.ord * (u : Ordinal)) := by
    apply ordinalTowerLevel_antitone _ _ (ordinal_initial_finite_power_top_level c hu t ht0)
    exact mul_le_mul_left' (by exact_mod_cast Nat.le.intro huv) c.ord
  have hθeq : c.ord ^ (u : Ordinal) * c.ord ^ (v : Ordinal) = c.ord ^ (t : Ordinal) := by
    rw [← Ordinal.opow_add, ← Nat.cast_add, huv]
  have hρ : c.ord * (t : Ordinal) ≠ 0 :=
    mul_ne_zero hpos.ne' (by exact_mod_cast ht0.ne')
  have hne : F.Nonempty := by
    have h := hrank.mono (ordinalDerived_antitone hF.isClosed (Ordinal.zero_le (c.ord * (t : Ordinal))))
    simpa only [ordinalDerived_zero] using h
  obtain ⟨η, e, he, _⟩ := ordinal_compact_order_homeomorph hF hne
  have hη : c.ord ^ (t : Ordinal) ≤ η := by
    simpa only [ordinal_uncountable_initial_power_rank hu] using
      ordinal_power_le_compact_model e hρ hrank
  have hfull : Ordinal.lift.{u+1} (c.ord ^ (t : Ordinal)) ≤
      Ordinal.type (· < · : F → _ → Prop) := by
    rw [ordinal_type_compact_order_model e he]
    exact Ordinal.lift_le.mpr (hη.trans (Order.le_succ η))
  have hlarge : Ordinal.lift.{u+1}
      (Ordinal.omega0 ^ (c.ord * ((u-1 : ℕ) : Ordinal)) * Order.succ (c.ord ^ (v : Ordinal))) <
      Ordinal.type (· < · : F → _ → Prop) := by
    rw [ordinal_uncountable_initial_power_rank hu]
    apply (Ordinal.lift_lt.mpr ?_).trans_le hfull
    have ht := ordinal_initial_packet_threshold_lt hu.le
      (Ordinal.opow_pos ((u-1 : ℕ) : Ordinal) hpos) v
    have he : c.ord ^ ((u-1 : ℕ) : Ordinal) * c.ord = c.ord ^ (u : Ordinal) := by
      have huone : ((u-1 : ℕ) : Ordinal.{u}) + 1 = (u : Ordinal) := by
        exact_mod_cast Nat.sub_add_cancel (show 1 ≤ u by omega)
      rw [← Ordinal.opow_succ, ← Ordinal.add_one_eq_succ, huone]
    simpa only [← mul_assoc, he, hθeq] using ht
  obtain ⟨y, hyo, hyrank⟩ := ordinalTower_exists_high_upper_cell_uniform
    hupper hretained hθlevel (β := c.ord ^ (v : Ordinal))
    (by rw [ordinal_uncountable_initial_power_rank hu, hθeq]) hF hFθ hlarge
  have hb : c.ord * ((m-1 : ℕ) : Ordinal) ≠ 0 :=
    mul_ne_zero hpos.ne' (by exact_mod_cast (show m-1 ≠ 0 by omega))
  have habs : 1 + c.ord * ((m-1 : ℕ) : Ordinal) = c.ord * ((m-1 : ℕ) : Ordinal) :=
    Ordinal.one_add_of_omega0_le ((Cardinal.omega0_le_ord.mpr hu.le).trans
      (Ordinal.le_mul_left c.ord (by exact_mod_cast (show 0 < m-1 by omega))))
  apply ordinalSeparatedBandCoreGeometry_of_isolated_upper_cell hθlevel y hyo hF hFθ hb habs
  · rw [hranks]
    exact mul_le_mul_left' (by exact_mod_cast Nat.sub_le u 1) c.ord
  · rwa [hranks]

end Posets
