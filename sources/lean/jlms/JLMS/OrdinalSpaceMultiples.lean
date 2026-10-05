import JLMS.OrdinalScattered
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# The block sequence in a multiple of an ordinal

Kislyakov Corollary 3.1 applies the transfinite block decomposition to
the sequence λξ=κξ. This file supplies its actual continuous interval map,
strict monotonicity, endpoints, and successor-gap computation.
-/

noncomputable section
namespace JLMS
universe u

def ordinalMultipleMap (κ γ : Ordinal.{u}) (hκ : 0 < κ) :
    C(OrdinalInterval γ, OrdinalInterval (κ * γ)) where
  toFun x := ⟨κ * x.val, Ordinal.zero_le _, mul_le_mul_left' x.property.2 κ⟩
  continuous_toFun :=
    ((Ordinal.isNormal_mul_right hκ).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem ordinalMultipleMap_val (κ γ : Ordinal.{u}) (hκ : 0 < κ)
    (x : OrdinalInterval γ) : (ordinalMultipleMap κ γ hκ x).val = κ * x.val := rfl

theorem ordinalMultipleMap_strictMono (κ γ : Ordinal.{u}) (hκ : 0 < κ) :
    StrictMono (ordinalMultipleMap κ γ hκ) := by
  intro x y hxy
  exact (Ordinal.isNormal_mul_right hκ).strictMono hxy

@[simp] theorem ordinalMultipleMap_zero (κ γ : Ordinal.{u}) (hκ : 0 < κ) :
    ordinalMultipleMap κ γ hκ ⟨0, le_rfl, Ordinal.zero_le _⟩ =
      ⟨0, le_rfl, Ordinal.zero_le _⟩ := Subtype.ext (mul_zero κ)

@[simp] theorem ordinalMultipleMap_endpoint (κ γ : Ordinal.{u}) (hκ : 0 < κ) :
    ordinalMultipleMap κ γ hκ ⟨γ, Ordinal.zero_le _, le_rfl⟩ =
      ⟨κ * γ, Ordinal.zero_le _, le_rfl⟩ := rfl

theorem ordinalMultipleMap_successor_gap (κ γ : Ordinal.{u}) (hκ : 0 < κ)
    (ξ : Ordinal.{u}) (hξ : ξ < γ) :
    (ordinalMultipleMap κ γ hκ
      ⟨Order.succ ξ, Ordinal.zero_le _, Order.succ_le_iff.mpr hξ⟩).val -
      (ordinalMultipleMap κ γ hκ ⟨ξ, Ordinal.zero_le _, hξ.le⟩).val = κ := by
  simp only [ordinalMultipleMap_val, Ordinal.mul_succ, Ordinal.add_sub_cancel]

theorem ordinalMultipleMap_infinite_successor_gap (κ γ : Ordinal.{u})
    (hκ : Ordinal.omega0 ≤ κ) (ξ : Ordinal.{u}) (hξ : ξ < γ) :
    Ordinal.omega0 ≤
      (ordinalMultipleMap κ γ (Ordinal.omega0_pos.trans_le hκ)
        ⟨Order.succ ξ, Ordinal.zero_le _, Order.succ_le_iff.mpr hξ⟩).val -
      (ordinalMultipleMap κ γ (Ordinal.omega0_pos.trans_le hκ)
        ⟨ξ, Ordinal.zero_le _, hξ.le⟩).val := by
  simpa only [ordinalMultipleMap_val, Ordinal.mul_succ, Ordinal.add_sub_cancel] using hκ

end JLMS
