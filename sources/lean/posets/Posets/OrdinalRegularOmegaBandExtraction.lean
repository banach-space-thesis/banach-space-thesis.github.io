import Posets.OrdinalRegularOmegaBandParameters
import Posets.OrdinalClosedCopyBandCells

/-! The actual finite band extraction with all ordinal arithmetic discharged.
A compact core of full source rank in κ^((N+1)m) supplies the selected upper
cell and a lower-ceiling image containing [0,κ^m], for every band k<N. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

theorem ordinalRegularOmega_exists_band_geometry
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (N m k : ℕ) (hm : 0 < m) (hk : k < N)
    (F : Set Ordinal.{u}) (hF : IsCompact F)
    (hFθ : F ⊆ Iic (c.ord ^ (((N+1)*m : ℕ) : Ordinal)))
    (hrank : (ordinalDerived F (c.ord * (((N+1)*m : ℕ) : Ordinal))).Nonempty) :
    Nonempty (OrdinalBandCoreGeometry F (c.ord ^ (((N+1)*m : ℕ) : Ordinal))
      (c.ord * ((k*m : ℕ) : Ordinal)) (c.ord * (m : Ordinal))) := by
  let t : ℕ := (N+1)*m
  let u : ℕ := (k+1)*m
  let v : ℕ := (N-k)*m
  have hu0 : 0 < u := Nat.mul_pos (Nat.succ_pos k) hm
  have hv0 : 0 < v := Nat.mul_pos (Nat.sub_pos_of_lt hk) hm
  have ht0 : 0 < t := Nat.mul_pos (Nat.succ_pos N) hm
  have huv : u + v = t := by
    dsimp only [u, v, t]
    rw [← Nat.add_mul]
    congr 1
    omega
  have hun : u - 1 + 1 = u := Nat.sub_add_cancel hu0
  have hvn : 1 + (v - 1) = v := by omega
  have htotal : (u - 1 + 1) + (1 + (v - 1)) = t := by omega
  have hranks : c.ord * ((k*m : ℕ) : Ordinal) + c.ord * (m : Ordinal) =
      c.ord * (u : Ordinal) := by
    simp only [u, Nat.add_mul, one_mul, Nat.cast_add, mul_add]
  have hb : c.ord * (m : Ordinal) ≠ 0 :=
    mul_ne_zero hc.ord_pos.ne' (by exact_mod_cast hm.ne')
  have habs : 1 + c.ord * (m : Ordinal) = c.ord * (m : Ordinal) :=
    Ordinal.one_add_of_omega0_le ((Cardinal.omega0_le_ord.mpr hc.aleph0_le).trans
      (Ordinal.le_mul_left c.ord (by exact_mod_cast hm)))
  have hscale : Ordinal.omega0 ^
      (c.ord * ((k*m : ℕ) : Ordinal) + c.ord * (m : Ordinal)) =
      c.ord ^ ((u - 1 : ℕ) + 1 : Ordinal) := by
    rw [hranks, ordinal_uncountable_initial_power_rank hu]
    congr 1
    exact_mod_cast hun.symm
  have hθlevel : c.ord ^ (t : Ordinal) ∈ ordinalTowerLevel (c.ord ^ (t : Ordinal))
      (c.ord * ((k*m : ℕ) : Ordinal) + c.ord * (m : Ordinal)) := by
    rw [hranks]
    apply ordinalTowerLevel_antitone _ _ (ordinal_initial_finite_power_top_level c hu t ht0)
    exact mul_le_mul_left' (by exact_mod_cast Nat.le.intro huv) c.ord
  have hθeq : c.ord ^ (t : Ordinal) =
      c.ord ^ ((u - 1 : ℕ) + 1 : Ordinal) * (c.ord * c.ord ^ ((v - 1 : ℕ) : Ordinal)) := by
    rw [← Ordinal.opow_one_add, ← Ordinal.opow_add]
    congr 1
    exact_mod_cast htotal.symm
  have hρ : c.ord * (t : Ordinal) ≠ 0 :=
    mul_ne_zero hc.ord_pos.ne' (by exact_mod_cast ht0.ne')
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
  apply ordinalBandCoreGeometry_of_upper_packet hc (u-1) hb habs hscale hθlevel
    (β := c.ord ^ ((v-1 : ℕ) : Ordinal)) hθeq.le hF hFθ
  apply (Ordinal.lift_lt.mpr (ordinal_regular_packet_threshold_lt hc
    (Ordinal.opow_pos _ hc.ord_pos) (v-1))).trans_le
  simpa only [← hθeq] using hfull

end Posets
