import Posets.OrdinalClosedCopySeparatedExtraction
import Mathlib.SetTheory.Ordinal.Principal

/-! Finite bands at arbitrary ordinal ranks. Doubling the band spacing
leaves room for a uniform loss of rank when extracting a single upper cell.
The resulting lower image still contains the prescribed ω-power. No
regularity or countability assumption on the rank is imposed. -/
noncomputable section
namespace Posets
open Set Topology Order
open ThesisCommon
universe u
set_option maxHeartbeats 1000000

theorem ordinal_finite_band_threshold_lt
    (b : Ordinal.{u}) (hb : b ≠ 0) (N k : ℕ) (hk : k ≤ N) :
    Ordinal.omega0 ^ (b * ((2*k : ℕ) : Ordinal) + b) *
        Order.succ (Ordinal.omega0 ^ (b * ((2*(N-k) : ℕ) : Ordinal))) <
      Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)) := by
  have hp : 0 < b := Ordinal.pos_iff_ne_zero.mpr hb
  have hret : b * ((2*k : ℕ) : Ordinal) + b = b * ((2*k+1 : ℕ) : Ordinal) := by
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  have hsum : (2*k+1) + 2*(N-k) = 2*N+1 := by omega
  rw [Ordinal.mul_succ, ← Ordinal.opow_add, hret, ← mul_add, ← Nat.cast_add, hsum]
  apply Ordinal.principal_add_omega0_opow
  · apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast (show 2*N+1 < 2*N+2 by omega)) hp
  · apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast (show 2*k+1 < 2*N+2 by omega)) hp

theorem ordinal_finite_band_power_decomposition
    (b : Ordinal.{u}) (N k : ℕ) (hk : k ≤ N) :
    Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)) =
      Ordinal.omega0 ^ (b * ((2*k+2 : ℕ) : Ordinal)) *
        Ordinal.omega0 ^ (b * ((2*(N-k) : ℕ) : Ordinal)) := by
  rw [← Ordinal.opow_add, ← mul_add, ← Nat.cast_add]
  have hsum : 2*N+2 = (2*k+2) + 2*(N-k) := by omega
  exact congrArg (fun n : ℕ => Ordinal.omega0 ^ (b * (n : Ordinal))) hsum

theorem ordinal_finite_band_exists_geometry
    (b : Ordinal.{u}) (hb : b ≠ 0) (habs : 1 + b = b)
    (N k : ℕ) (hk : k ≤ N)
    (F : Set Ordinal.{u}) (hF : IsCompact F)
    (hFθ : F ⊆ Iic (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal))))
    (hrank : (ordinalDerived F (b * ((2*N+2 : ℕ) : Ordinal))).Nonempty) :
    Nonempty (OrdinalSeparatedBandCoreGeometry F
      (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)))
      (b * ((2*k+2 : ℕ) : Ordinal)) (b * ((2*k : ℕ) : Ordinal)) b) := by
  have htotal : b * ((2*N+2 : ℕ) : Ordinal) ≠ 0 :=
    mul_ne_zero hb (by exact_mod_cast (show 2*N+2 ≠ 0 by omega))
  have hne : F.Nonempty := by
    have hh := hrank.mono (ordinalDerived_antitone hF.isClosed
      (Ordinal.zero_le (b * ((2*N+2 : ℕ) : Ordinal))))
    simpa only [ordinalDerived_zero] using hh
  obtain ⟨η, e, he, _⟩ := ordinal_compact_order_homeomorph hF hne
  have hη := ordinal_power_le_compact_model e htotal hrank
  have hfull : Ordinal.lift.{u+1} (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal))) ≤
      Ordinal.type (· < · : F → _ → Prop) := by
    rw [ordinal_type_compact_order_model e he]
    exact Ordinal.lift_le.mpr (hη.trans (Order.le_succ η))
  have heq := ordinal_finite_band_power_decomposition b N k hk
  have hθ : Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)) ∈
      ordinalTowerLevel (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)))
        (b * ((2*k+2 : ℕ) : Ordinal)) := by
    rw [heq]
    exact ordinalTowerLevel_contains_power_grid _ _
      (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero) le_rfl
  apply ordinalSeparatedBandCoreGeometry_of_uniform_order_bound hθ heq.le hF hFθ hb habs
  · have hret : b * ((2*k : ℕ) : Ordinal) + b = b * ((2*k+1 : ℕ) : Ordinal) := by
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    rw [hret]
    exact mul_le_mul_left' (by exact_mod_cast (show 2*k+1 ≤ 2*k+2 by omega)) b
  · exact (Ordinal.lift_lt.mpr (ordinal_finite_band_threshold_lt b hb N k hk)).trans_le hfull

end Posets
