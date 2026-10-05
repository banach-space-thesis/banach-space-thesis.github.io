import Posets.OrdinalClosedCopyUpperCell
import Posets.OrdinalClosedCopyFiberTypes

/-! Uniform bounds on ceiling fibers give a large actual clopen upper cell.
The retained fiber rank can be lower than the arithmetic upper level. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalCeiling_exists_large_upper_fiber_uniform
    {A F : Set Ordinal.{u}} {θ δ μ β : Ordinal.{u}}
    (hA : IsCompact A) (hθ : θ ∈ A) (hδ : δ ≠ 0)
    (hdiv : ∀ y ∈ A, δ ∣ y) (hθbound : θ ≤ δ * β)
    (hFθ : F ⊆ Iic θ)
    (hlarge : Ordinal.lift.{u+1} (μ * Order.succ β) <
      Ordinal.type (· < · : F → _ → Prop)) :
    ∃ y : Ordinal.{u}, Ordinal.lift.{u+1} μ <
      Ordinal.type (· < · : (F ∩ {x | ordinalCeiling A x = y} : Set Ordinal.{u}) → _ → Prop) := by
  classical
  let f (x : F) : Iic β := ⟨ordinalCeiling A x.val / δ,
    Ordinal.div_le_of_le_mul ((ordinalCeiling_le_of_mem hθ (hFθ x.property)).trans hθbound)⟩
  have hf : Monotone f := fun x x' h =>
    Ordinal.div_le_left (ordinalCeiling_mono hA ⟨θ, hθ⟩ h) δ
  by_contra hn
  have hsmall (y : Iic β) :
      Ordinal.type (· < · : {x : F // f x = y} → _ → Prop) ≤ Ordinal.lift.{u+1} μ := by
    have htarget : Ordinal.type
        (· < · : (F ∩ {x | ordinalCeiling A x = δ * y.val} : Set Ordinal.{u}) → _ → Prop) ≤
          Ordinal.lift.{u+1} μ := le_of_not_gt (fun h => hn ⟨δ * y.val, h⟩)
    let e (x : {x : F // f x = y}) :
        (F ∩ {x | ordinalCeiling A x = δ * y.val} : Set Ordinal.{u}) :=
      ⟨x.val.val, x.val.property, by
        have hd := Ordinal.div_mul_cancel hδ
          (hdiv _ (ordinalCeiling_mem hA ⟨θ, hθ⟩ x.val.val))
        exact hd.symm.trans (congrArg (fun z => δ * z) (congrArg Subtype.val x.property))⟩
    have he : StrictMono e := fun _ _ h => h
    exact (RelEmbedding.ofMonotone e he).ordinal_type_le.trans htarget
  have ht := ordinal_type_le_mul_of_monotone_fibers f hf
    (Ordinal.lift.{u+1} μ) hsmall
  rw [ordinal_type_Iic, ← Ordinal.lift_mul] at ht
  exact hlarge.not_ge ht

theorem ordinalTower_exists_high_upper_cell_uniform
    {F : Set Ordinal.{u}} {θ β upperRank retainedRank : Ordinal.{u}}
    (hupper : upperRank ≠ 0) (hretained : retainedRank ≠ 0)
    (hθ : θ ∈ ordinalTowerLevel θ upperRank)
    (hθbound : θ ≤ Ordinal.omega0 ^ upperRank * β)
    (hF : IsCompact F) (hFθ : F ⊆ Iic θ)
    (hlarge : Ordinal.lift.{u+1} (Ordinal.omega0 ^ retainedRank * Order.succ β) <
      Ordinal.type (· < · : F → _ → Prop)) :
    ∃ y : ordinalTowerLevel θ upperRank,
      IsOpen ({y} : Set (ordinalTowerLevel θ upperRank)) ∧
      (ordinalDerived (F ∩ {x | ordinalCeiling
        (ordinalTowerLevel θ upperRank) x = y.val}) retainedRank).Nonempty := by
  have hA := ordinalTowerLevel_isCompact θ upperRank
  have hd (y : Ordinal.{u}) (hy : y ∈ ordinalTowerLevel θ upperRank) :
      Ordinal.omega0 ^ upperRank ∣ y := by
    rw [ordinalTowerLevel, ordinalDerived_Iic, ordinalDerived_univ, if_neg hupper] at hy
    exact hy.1.2
  obtain ⟨y, hy⟩ := ordinalCeiling_exists_large_upper_fiber_uniform hA hθ
    (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero) hd hθbound hFθ hlarge
  let C : Set Ordinal.{u} := F ∩ {x | ordinalCeiling (ordinalTowerLevel θ upperRank) x = y}
  have hC : IsCompact C := hF.inter_right
    (isClosed_singleton.preimage (ordinalCeiling_continuous hA ⟨θ, hθ⟩))
  have hδ : IsSuccLimit (Ordinal.omega0 ^ retainedRank) :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hretained
  have ht : Ordinal.lift.{u+1} (Order.succ (Ordinal.omega0 ^ retainedRank)) ≤
      Ordinal.type (· < · : C → _ → Prop) := by
    rw [Ordinal.lift_succ]
    exact Order.succ_le_iff.mpr hy
  obtain ⟨hyA, hyo⟩ := ordinalCeiling_isolated_of_compact_large_fiber hA hθ hC
    (fun _ hx => hFθ hx.1) (fun _ hx => hx.2) hδ ht
  exact ⟨⟨y, hyA⟩, hyo, ordinalClosedCore_rank_of_order_type hC hretained ht⟩

end Posets
