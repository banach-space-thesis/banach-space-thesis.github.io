import JLMS.OrdinalSpacePowerBlocks

/-! The actual cofinal block embedding associated with an arbitrary
strictly increasing sequence of positive finite exponents. -/

noncomputable section
open Set Order
namespace Posets
universe u
set_option maxHeartbeats 800000

def ordinalOmegaFiniteIndex (ξ : Ordinal.{u}) (hξ : ξ < Ordinal.omega0) : ℕ :=
  (Ordinal.lt_omega0.mp hξ).choose

theorem ordinalOmegaFiniteIndex_spec (ξ : Ordinal.{u}) (hξ : ξ < Ordinal.omega0) :
    ξ = (ordinalOmegaFiniteIndex ξ hξ : Ordinal) :=
  (Ordinal.lt_omega0.mp hξ).choose_spec

@[simp] theorem ordinalOmegaFiniteIndex_nat (n : ℕ)
    (hn : (n : Ordinal.{u}) < Ordinal.omega0) :
    ordinalOmegaFiniteIndex (n : Ordinal.{u}) hn = n := by
  exact_mod_cast (ordinalOmegaFiniteIndex_spec (n : Ordinal.{u}) hn).symm

def ordinalOmegaNatIndexEquiv : ℕ ≃ Iio (Ordinal.omega0 : Ordinal.{u}) where
  toFun n := ⟨n, Ordinal.nat_lt_omega0 n⟩
  invFun ξ := ordinalOmegaFiniteIndex ξ.val ξ.property
  left_inv n := ordinalOmegaFiniteIndex_nat n _
  right_inv ξ := Subtype.ext (ordinalOmegaFiniteIndex_spec ξ.val ξ.property).symm

def ordinalOmegaHeightPredecessor (h : ℕ → ℕ) (ξ : Ordinal.{u}) : Ordinal.{u} :=
  if hξ : ξ < Ordinal.omega0 then ((h (ordinalOmegaFiniteIndex ξ hξ) - 1 : ℕ) : Ordinal)
  else Ordinal.omega0 + ξ

@[simp] theorem ordinalOmegaHeightPredecessor_nat (h : ℕ → ℕ) (n : ℕ) :
    ordinalOmegaHeightPredecessor h (n : Ordinal.{u}) = ((h n - 1 : ℕ) : Ordinal) := by
  simp [ordinalOmegaHeightPredecessor, Ordinal.nat_lt_omega0]

theorem ordinalOmegaHeightPredecessor_strictMono (h : ℕ → ℕ)
    (hh : StrictMono h) (h0 : 1 ≤ h 0) : StrictMono (ordinalOmegaHeightPredecessor.{u} h) := by
  intro ξ η hξη
  by_cases hη : η < Ordinal.omega0
  · have hξ := hξη.trans hη
    obtain ⟨i, rfl⟩ := Ordinal.lt_omega0.mp hξ
    obtain ⟨j, rfl⟩ := Ordinal.lt_omega0.mp hη
    simp only [ordinalOmegaHeightPredecessor_nat]
    have hij : i < j := by exact_mod_cast hξη
    have hi : 1 ≤ h i := h0.trans (hh.monotone (Nat.zero_le i))
    have hlt := hh hij
    exact_mod_cast (by omega : h i - 1 < h j - 1)
  · by_cases hξ : ξ < Ordinal.omega0
    · simp only [ordinalOmegaHeightPredecessor, dif_pos hξ, dif_neg hη]
      exact (Ordinal.nat_lt_omega0 _).trans_le (Ordinal.le_add_right _ _)
    · simp only [ordinalOmegaHeightPredecessor, dif_neg hξ, dif_neg hη]
      exact (Ordinal.isNormal_add_right Ordinal.omega0).strictMono hξη

def ordinalOmegaHeightNormal (h : ℕ → ℕ) : Ordinal.{u} → Ordinal.{u} :=
  JLMS.ordinalInitialSup (ordinalOmegaHeightPredecessor h)

theorem ordinalOmegaHeightNormal_isNormal (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    Ordinal.IsNormal (ordinalOmegaHeightNormal.{u} h) :=
  JLMS.ordinalInitialSup_isNormal _ (ordinalOmegaHeightPredecessor_strictMono h hh h0)

@[simp] theorem ordinalOmegaHeightNormal_zero (h : ℕ → ℕ) :
    ordinalOmegaHeightNormal.{u} h 0 = 0 := JLMS.ordinalInitialSup_zero _

theorem ordinalOmegaHeightNormal_succ (h : ℕ → ℕ) (hh : StrictMono h)
    (h0 : 1 ≤ h 0) (n : ℕ) :
    ordinalOmegaHeightNormal h ((n + 1 : ℕ) : Ordinal.{u}) = (h n : Ordinal) := by
  rw [Ordinal.natCast_succ, ordinalOmegaHeightNormal, JLMS.ordinalInitialSup_succ _
    (ordinalOmegaHeightPredecessor_strictMono h hh h0).monotone,
    ordinalOmegaHeightPredecessor_nat, ← Ordinal.natCast_succ]
  exact_mod_cast Nat.sub_add_cancel (h0.trans (hh.monotone (Nat.zero_le n)))

theorem ordinalOmegaHeightNormal_omega (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ordinalOmegaHeightNormal.{u} h Ordinal.omega0 = Ordinal.omega0 := by
  apply le_antisymm
  · apply Ordinal.blsub_le
    intro ξ hξ
    simp only [ordinalOmegaHeightPredecessor, dif_pos hξ]
    exact Ordinal.nat_lt_omega0 _
  · exact (ordinalOmegaHeightNormal_isNormal h hh h0).le_apply

def ordinalOmegaBlockPower (κ : Ordinal.{u}) (h : ℕ → ℕ) : Ordinal.{u} → Ordinal.{u} :=
  JLMS.ordinalResetZero (fun ξ => κ ^ ordinalOmegaHeightNormal h ξ)

theorem ordinalOmegaBlockPower_isNormal (κ : Ordinal.{u}) (hκ : 1 < κ)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    Ordinal.IsNormal (ordinalOmegaBlockPower κ h) :=
  JLMS.ordinalResetZero_isNormal _ ((Ordinal.isNormal_opow hκ).comp
    (ordinalOmegaHeightNormal_isNormal h hh h0))

@[simp] theorem ordinalOmegaBlockPower_zero (κ : Ordinal.{u}) (h : ℕ → ℕ) :
    ordinalOmegaBlockPower κ h 0 = 0 := JLMS.ordinalResetZero_zero _

theorem ordinalOmegaBlockPower_succ (κ : Ordinal.{u}) (h : ℕ → ℕ)
    (hh : StrictMono h) (h0 : 1 ≤ h 0) (n : ℕ) :
    ordinalOmegaBlockPower κ h ((n + 1 : ℕ) : Ordinal) = κ ^ (h n : Ordinal) := by
  rw [ordinalOmegaBlockPower, JLMS.ordinalResetZero_of_ne_zero _ (by
    exact_mod_cast Nat.succ_ne_zero n), ordinalOmegaHeightNormal_succ h hh h0]

theorem ordinalOmegaBlockPower_endpoint (κ : Ordinal.{u}) (h : ℕ → ℕ)
    (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ordinalOmegaBlockPower κ h Ordinal.omega0 = κ ^ Ordinal.omega0 := by
  rw [ordinalOmegaBlockPower, JLMS.ordinalResetZero_of_ne_zero _ Ordinal.omega0_ne_zero,
    ordinalOmegaHeightNormal_omega h hh h0]

def ordinalOmegaBlockMap (κ : Ordinal.{u}) (hκ : 1 < κ)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    C(JLMS.OrdinalInterval (Ordinal.omega0 : Ordinal.{u}), JLMS.OrdinalInterval (κ ^ Ordinal.omega0)) where
  toFun ξ := ⟨ordinalOmegaBlockPower κ h ξ.val, Ordinal.zero_le _, by
    simpa only [ordinalOmegaBlockPower_endpoint κ h hh h0] using
      (ordinalOmegaBlockPower_isNormal κ hκ h hh h0).monotone ξ.property.2⟩
  continuous_toFun := ((ordinalOmegaBlockPower_isNormal κ hκ h hh h0).continuous.comp
    continuous_subtype_val).subtype_mk _

theorem ordinalOmegaBlockMap_strictMono (κ : Ordinal.{u}) (hκ : 1 < κ)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    StrictMono (ordinalOmegaBlockMap κ hκ h hh h0) := by
  intro x y hxy
  exact (ordinalOmegaBlockPower_isNormal κ hκ h hh h0).strictMono hxy

@[simp] theorem ordinalOmegaBlockMap_zero (κ : Ordinal.{u}) (hκ : 1 < κ)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ordinalOmegaBlockMap κ hκ h hh h0 ⟨0, le_rfl, Ordinal.zero_le _⟩ =
      ⟨0, le_rfl, Ordinal.zero_le _⟩ := Subtype.ext (ordinalOmegaBlockPower_zero κ h)

@[simp] theorem ordinalOmegaBlockMap_endpoint (κ : Ordinal.{u}) (hκ : 1 < κ)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ordinalOmegaBlockMap κ hκ h hh h0 ⟨Ordinal.omega0, Ordinal.zero_le _, le_rfl⟩ =
      ⟨κ ^ Ordinal.omega0, Ordinal.zero_le _, le_rfl⟩ :=
  Subtype.ext (ordinalOmegaBlockPower_endpoint κ h hh h0)

theorem ordinalOmegaBlockMap_length (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) (n : ℕ) :
    JLMS.ordinalSpaceBlockLength
      (ordinalOmegaBlockMap c.ord (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc))
        h hh h0) (ordinalOmegaNatIndexEquiv n) = c.ord ^ (h n : Ordinal) := by
  let hκ := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)
  have hs := (ordinalOmegaBlockPower_isNormal c.ord hκ h hh h0).strictMono
    (Order.lt_succ (n : Ordinal.{u}))
  rw [← Ordinal.natCast_succ, ordinalOmegaBlockPower_succ c.ord h hh h0] at hs
  have ha := Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc)
      (h n : Ordinal)) _ hs
  change ordinalOmegaBlockPower c.ord h (Order.succ (n : Ordinal)) -
    ordinalOmegaBlockPower c.ord h (n : Ordinal) = _
  rw [← Ordinal.natCast_succ, ordinalOmegaBlockPower_succ c.ord h hh h0]
  calc
    _ = (ordinalOmegaBlockPower c.ord h (n : Ordinal) + c.ord ^ (h n : Ordinal)) -
        ordinalOmegaBlockPower c.ord h (n : Ordinal) := by rw [ha]
    _ = _ := Ordinal.add_sub_cancel _ _

theorem ordinalOmegaBlockMap_infinite_blocks (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (ξ : Iio (Ordinal.omega0 : Ordinal.{u})) :
    Ordinal.omega0 ≤ JLMS.ordinalSpaceBlockLength
      (ordinalOmegaBlockMap c.ord (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc))
        h hh h0) ξ := by
  obtain ⟨n, rfl⟩ := ordinalOmegaNatIndexEquiv.surjective ξ
  rw [ordinalOmegaBlockMap_length c hc h hh h0 n]
  have hn : (1 : Ordinal.{u}) ≤ (h n : Ordinal) := by
    exact_mod_cast h0.trans (hh.monotone (Nat.zero_le n))
  exact (Cardinal.omega0_le_ord.mpr hc).trans (by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right
      (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc)) hn)

end Posets
