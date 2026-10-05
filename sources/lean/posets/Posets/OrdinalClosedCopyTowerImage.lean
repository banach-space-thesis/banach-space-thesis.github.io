import Posets.OrdinalClosedCopyCeilingImageRank
import Posets.CountableOrdinalPFPCanonicalNodes

/-! The lower-level projection of a high-rank compact core retains a large
ordinal interval.  The projection is the actual canonical tower ceiling. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalTowerLevel_contains_power_grid (θ a : Ordinal.{u})
    {q : Ordinal.{u}} (hq : q ≠ 0) (hθ : Ordinal.omega0 ^ a * q ≤ θ) :
    Ordinal.omega0 ^ a * q ∈ ordinalTowerLevel θ a := by
  rw [ordinalTowerLevel, ordinalDerived_Iic, ordinalDerived_univ]
  by_cases ha : a = 0
  · rw [if_pos ha]
    exact ⟨mem_univ _, hθ⟩
  · rw [if_neg ha]
    exact ⟨⟨mul_ne_zero (Ordinal.opow_ne_zero a Ordinal.omega0_ne_zero) hq,
      ⟨q, rfl⟩⟩, hθ⟩

theorem ordinalTowerCeiling_image_model_rank
    {F : Set Ordinal.{u}} {θ a b : Ordinal.{u}}
    (hθ : θ ∈ ordinalTowerLevel θ a)
    (hF : IsCompact F) (hFθ : F ⊆ Iic θ) (hb : b ≠ 0)
    (hrank : (ordinalDerived F (Order.succ a + b)).Nonempty) :
    ∃ β : Ordinal.{u},
      ∃ e : OrdinalInterval β ≃ₜ (ordinalCeiling (ordinalTowerLevel θ a) '' F),
        StrictMono (fun x => (e x).val) ∧ Ordinal.omega0 ^ b ≤ β :=
  ordinalCeiling_image_model_rank (ordinalTowerLevel_isCompact θ a) hθ
    (fun _ hq hqθ => ordinalTowerLevel_contains_power_grid θ a hq hqθ)
    hF hFθ hb hrank

theorem ordinalTowerCeiling_image_model_rank_of_succ_absorbed
    {F : Set Ordinal.{u}} {θ a b : Ordinal.{u}}
    (hθ : θ ∈ ordinalTowerLevel θ a)
    (hF : IsCompact F) (hFθ : F ⊆ Iic θ) (hb : b ≠ 0)
    (habs : 1 + b = b)
    (hrank : (ordinalDerived F (a + b)).Nonempty) :
    ∃ β : Ordinal.{u},
      ∃ e : OrdinalInterval β ≃ₜ (ordinalCeiling (ordinalTowerLevel θ a) '' F),
        StrictMono (fun x => (e x).val) ∧ Ordinal.omega0 ^ b ≤ β := by
  apply ordinalTowerCeiling_image_model_rank hθ hF hFθ hb
  simpa only [← Ordinal.add_one_eq_succ, add_assoc, habs] using hrank

end Posets
