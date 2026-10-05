import Posets.OrdinalClosedCopyFiberTypes
import ThesisCommon.Analysis.OrdinalRetraction

/-! A closed ordinal level containing a complete arithmetic grid has ceiling
fibers no longer than one grid interval.  This controls the actual fibers,
including those at limit junctions. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

theorem ordinalCeiling_fiber_type_le_grid
    {A : Set Ordinal.{u}} {θ δ : Ordinal.{u}}
    (hA : IsCompact A) (hθ : θ ∈ A) (hδ : δ ≠ 0)
    (hgrid : ∀ q : Ordinal.{u}, q ≠ 0 → δ * q ≤ θ → δ * q ∈ A)
    (y : Ordinal.{u}) :
    Ordinal.type (· < · : {x : Iic θ // ordinalCeiling A x = y} → _ → Prop) ≤
      Ordinal.lift.{u+1} (Order.succ δ) := by
  classical
  let F := {x : Iic θ // ordinalCeiling A x = y}
  by_cases hn : Nonempty F
  · let B : Set Ordinal.{u} := {x | x ≤ θ ∧ ordinalCeiling A x = y}
    have hB : B.Nonempty := by
      obtain ⟨x⟩ := hn
      exact ⟨x.val.val, x.val.property, x.property⟩
    let z := sInf B
    have hz : z ∈ B := csInf_mem hB
    let b := δ * (z / δ)
    have hbz : b ≤ z := Ordinal.mul_div_le z δ
    have hzupper : z < b + δ := by
      rw [← Ordinal.div_add_mod z δ]
      exact add_lt_add_left (Ordinal.mod_lt _ hδ) _
    have hyupper : y ≤ b + δ := by
      rw [← hz.2]
      by_cases ht : b + δ ≤ θ
      · have he : b + δ = δ * Order.succ (z / δ) := by
          rw [Ordinal.mul_succ]
        exact ordinalCeiling_le_of_mem
          (he ▸ hgrid (Order.succ (z / δ)) (Ordinal.succ_ne_zero _) (he ▸ ht)) hzupper.le
      · exact (ordinalCeiling_le_of_mem hθ hz.1).trans (le_of_not_ge ht)
    have hxlo (x : F) : b ≤ x.val.val :=
      hbz.trans (csInf_le' (show x.val.val ∈ B from ⟨x.val.property, x.property⟩))
    have hxhi (x : F) : x.val.val ≤ b + δ := by
      have hx := le_ordinalCeiling hA ⟨θ, hθ⟩
        (x.val.property.trans (le_csSup hA.bddAbove hθ))
      rw [x.property] at hx
      exact hx.trans hyupper
    let e (x : F) : Iic δ := ⟨x.val.val - b, Ordinal.sub_le.mpr (hxhi x)⟩
    have he : StrictMono e := by
      intro x x' hxx'
      change x.val.val - b < x'.val.val - b
      rw [Ordinal.sub_lt_of_le (hxlo x), Ordinal.add_sub_cancel_of_le (hxlo x')]
      exact hxx'
    have ht := (RelEmbedding.ofMonotone e he).ordinal_type_le
    exact ht.trans_eq (ordinal_type_Iic δ)
  · letI : IsEmpty F := not_nonempty_iff.mp hn
    rw [Ordinal.type_eq_zero_iff_isEmpty.mpr inferInstance]
    exact Ordinal.zero_le _

theorem ordinalCeiling_image_type_bound
    {A F : Set Ordinal.{u}} {θ δ : Ordinal.{u}}
    (hA : IsCompact A) (hθ : θ ∈ A) (hδ : δ ≠ 0)
    (hgrid : ∀ q : Ordinal.{u}, q ≠ 0 → δ * q ≤ θ → δ * q ∈ A)
    (hF : F ⊆ Iic θ) :
    Ordinal.type (· < · : F → _ → Prop) ≤
      Ordinal.lift.{u+1} (Order.succ δ) *
        Ordinal.type (· < · : (ordinalCeiling A '' F) → _ → Prop) := by
  let f (x : F) : ordinalCeiling A '' F := ⟨ordinalCeiling A x, ⟨x, x.property, rfl⟩⟩
  have hf : Monotone f := fun x x' h => ordinalCeiling_mono hA ⟨θ, hθ⟩ h
  apply ordinal_type_le_mul_of_monotone_fibers f hf
  intro y
  let e (x : {x : F // f x = y}) : {x : Iic θ // ordinalCeiling A x = y.val} :=
    ⟨⟨x.val.val, hF x.val.property⟩, congrArg Subtype.val x.property⟩
  have he : StrictMono e := fun _ _ h => h
  exact (RelEmbedding.ofMonotone e he).ordinal_type_le.trans
    (ordinalCeiling_fiber_type_le_grid hA hθ hδ hgrid y.val)

end Posets
