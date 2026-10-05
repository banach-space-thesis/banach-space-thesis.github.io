import JLMS.OrdinalSpaceCofinalSequence
import JLMS.OrdinalSpaceBlocksTopology
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# The power blocks for a limit exponent

The cofinal exponent sequence gives λ(ξ)=κ^h(ξ) at positive indices.
Changing λ(0) to zero preserves normality. For an infinite initial base κ,
every power is additively indecomposable, so each successor gap is exactly
the power at its right endpoint. This supplies all the geometric inputs
to Kislyakov's block decomposition in Corollary 3.2.
-/

noncomputable section
namespace JLMS
open Order
universe u

def ordinalResetZero (f : Ordinal.{u} → Ordinal.{u}) (ξ : Ordinal.{u}) : Ordinal.{u} :=
  if ξ = 0 then 0 else f ξ

@[simp] theorem ordinalResetZero_zero (f : Ordinal.{u} → Ordinal.{u}) :
    ordinalResetZero f 0 = 0 := if_pos rfl

theorem ordinalResetZero_of_ne_zero (f : Ordinal.{u} → Ordinal.{u})
    {ξ : Ordinal.{u}} (hξ : ξ ≠ 0) : ordinalResetZero f ξ = f ξ := if_neg hξ

theorem ordinalResetZero_isNormal (f : Ordinal.{u} → Ordinal.{u}) (hf : Ordinal.IsNormal f) :
    Ordinal.IsNormal (ordinalResetZero f) := by
  apply (Ordinal.isNormal_iff_strictMono_limit _).mpr
  constructor
  · intro ξ η hξη
    have hη : η ≠ 0 := (Ordinal.zero_le ξ |>.trans_lt hξη).ne'
    rw [ordinalResetZero_of_ne_zero f hη]
    by_cases hξ : ξ = 0
    · rw [hξ, ordinalResetZero_zero]
      exact (Ordinal.zero_le _).trans_lt (hf.strictMono hξη)
    · rw [ordinalResetZero_of_ne_zero f hξ]
      exact hf.strictMono hξη
  · intro ξ hξ a ha
    rw [ordinalResetZero_of_ne_zero f hξ.ne_bot]
    apply (hf.limit_le hξ).mpr
    intro η hη
    exact (hf.monotone (Order.le_succ η)).trans (by
      simpa only [ordinalResetZero_of_ne_zero f (Ordinal.succ_ne_zero η)] using
        ha (Order.succ η) (hξ.succ_lt hη))

def ordinalCofinalPower (κ γ : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  ordinalResetZero (fun ξ => κ ^ ordinalCofinalExponent γ ξ)

theorem ordinalCofinalPower_isNormal (κ γ : Ordinal.{u}) (hκ : 1 < κ) :
    Ordinal.IsNormal (ordinalCofinalPower κ γ) :=
  ordinalResetZero_isNormal _ ((Ordinal.isNormal_opow hκ).comp (ordinalCofinalExponent_isNormal γ))

@[simp] theorem ordinalCofinalPower_zero (κ γ : Ordinal.{u}) : ordinalCofinalPower κ γ 0 = 0 :=
  ordinalResetZero_zero _

theorem ordinalCofinalPower_of_ne_zero (κ γ : Ordinal.{u}) {ξ : Ordinal.{u}} (hξ : ξ ≠ 0) :
    ordinalCofinalPower κ γ ξ = κ ^ ordinalCofinalExponent γ ξ :=
  ordinalResetZero_of_ne_zero _ hξ

theorem ordinalCofinalPower_endpoint (κ γ : Ordinal.{u}) (hγ : IsSuccLimit γ) :
    ordinalCofinalPower κ γ γ.cof.ord = κ ^ γ := by
  have hcof : γ.cof.ord ≠ 0 := by
    simpa using (Ordinal.cof_ne_zero.mpr hγ.ne_bot)
  rw [ordinalCofinalPower_of_ne_zero κ γ hcof, ordinalCofinalExponent_endpoint γ hγ]

def ordinalCofinalPowerMap (κ γ : Ordinal.{u}) (hκ : 1 < κ) (hγ : IsSuccLimit γ) :
    C(OrdinalInterval γ.cof.ord, OrdinalInterval (κ ^ γ)) where
  toFun ξ := ⟨ordinalCofinalPower κ γ ξ.val, Ordinal.zero_le _, by
    simpa only [ordinalCofinalPower_endpoint κ γ hγ] using
      (ordinalCofinalPower_isNormal κ γ hκ).monotone ξ.prop.2⟩
  continuous_toFun :=
    ((ordinalCofinalPower_isNormal κ γ hκ).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem ordinalCofinalPowerMap_val (κ γ : Ordinal.{u}) (hκ : 1 < κ)
    (hγ : IsSuccLimit γ) (ξ : OrdinalInterval γ.cof.ord) :
    (ordinalCofinalPowerMap κ γ hκ hγ ξ).val = ordinalCofinalPower κ γ ξ.val := rfl

theorem ordinalCofinalPowerMap_strictMono (κ γ : Ordinal.{u}) (hκ : 1 < κ) (hγ : IsSuccLimit γ) :
    StrictMono (ordinalCofinalPowerMap κ γ hκ hγ) := by
  intro ξ η hξη
  exact (ordinalCofinalPower_isNormal κ γ hκ).strictMono hξη

@[simp] theorem ordinalCofinalPowerMap_zero (κ γ : Ordinal.{u}) (hκ : 1 < κ)
    (hγ : IsSuccLimit γ) :
    ordinalCofinalPowerMap κ γ hκ hγ ⟨0, le_rfl, Ordinal.zero_le _⟩ =
      ⟨0, le_rfl, Ordinal.zero_le _⟩ := Subtype.ext (ordinalCofinalPower_zero κ γ)

@[simp] theorem ordinalCofinalPowerMap_endpoint (κ γ : Ordinal.{u}) (hκ : 1 < κ)
    (hγ : IsSuccLimit γ) :
    ordinalCofinalPowerMap κ γ hκ hγ ⟨γ.cof.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨κ ^ γ, Ordinal.zero_le _, le_rfl⟩ := Subtype.ext (ordinalCofinalPower_endpoint κ γ hγ)

theorem ordinalCofinalPower_successor_gap (κ γ : Ordinal.{u}) (hκ : 1 < κ)
    (hp : Ordinal.Principal (· + ·) κ) (ξ : Ordinal.{u}) :
    ordinalCofinalPower κ γ (Order.succ ξ) - ordinalCofinalPower κ γ ξ =
      κ ^ ordinalCofinalExponent γ (Order.succ ξ) := by
  have hlt := (ordinalCofinalPower_isNormal κ γ hκ).strictMono (Order.lt_succ ξ)
  rw [ordinalCofinalPower_of_ne_zero κ γ (Ordinal.succ_ne_zero ξ)] at hlt ⊢
  have ha := Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_opow_of_principal_add hp (ordinalCofinalExponent γ (Order.succ ξ))) _ hlt
  calc
    _ = (ordinalCofinalPower κ γ ξ + κ ^ ordinalCofinalExponent γ (Order.succ ξ)) -
        ordinalCofinalPower κ γ ξ := congrArg (fun z => z - ordinalCofinalPower κ γ ξ) ha.symm
    _ = _ := Ordinal.add_sub_cancel _ _

theorem ordinalCofinalPowerMap_blockLength (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : IsSuccLimit γ) (ξ : Set.Iio γ.cof.ord) :
    ordinalSpaceBlockLength (ordinalCofinalPowerMap c.ord γ
      (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)) hγ) ξ =
        c.ord ^ ordinalCofinalExponent γ (Order.succ ξ.val) :=
  ordinalCofinalPower_successor_gap c.ord γ
    (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc))
    (Ordinal.principal_add_ord hc) ξ.val

theorem ordinalCofinalPowerMap_infinite_blocks (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : IsSuccLimit γ) (ξ : Set.Iio γ.cof.ord) :
    Ordinal.omega0 ≤ ordinalSpaceBlockLength (ordinalCofinalPowerMap c.ord γ
      (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)) hγ) ξ := by
  rw [ordinalCofinalPowerMap_blockLength c hc γ hγ ξ]
  have hbase : Ordinal.omega0 ≤ c.ord := Cardinal.omega0_le_ord.mpr hc
  calc
    Ordinal.omega0 ≤ c.ord := hbase
    _ = c.ord ^ (1 : Ordinal) := (Ordinal.opow_one c.ord).symm
    _ ≤ c.ord ^ ordinalCofinalExponent γ (Order.succ ξ.val) :=
      Ordinal.opow_le_opow_right (Ordinal.omega0_pos.trans_le hbase)
        ((show (1 : Ordinal) ≤ 2 from one_le_two).trans (two_le_ordinalCofinalExponent _ _))

end JLMS

