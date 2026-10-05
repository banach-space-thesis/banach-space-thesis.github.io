import Posets.OrdinalClosedCoreBands
import Mathlib.SetTheory.Cardinal.Ordinal

/-! Explicit compact clopen blocks in the half-open ordinal space. The
translated copy of [0,b] has range (a,b] when (a+1)+b=b. Finite powers of
an infinite initial ordinal supply these blocks below its first limit power. -/

noncomputable section
open Set Topology
universe u
namespace Posets

local instance outerBlockCompactIic (b : Ordinal.{u}) : CompactSpace (Iic b) :=
  isCompact_iff_compactSpace.mp (ordinalClosedCore_interval_compact b)

def ordinalOuterBlockMap (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b < Γ) :
    C(Iic b, Iio Γ) :=
  ⟨fun x => ⟨(a + 1) + x.val, by
      apply lt_of_le_of_lt ?_ hb
      simpa only [hshift] using add_le_add_left x.property (a + 1)⟩,
    ((Ordinal.isNormal_add_right (a + 1)).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem ordinalOuterBlockMap_apply
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b < Γ) (x : Iic b) :
    (ordinalOuterBlockMap a b Γ hshift hb x).val = (a + 1) + x.val := rfl

theorem ordinalOuterBlockMap_strictMono
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b < Γ) :
    StrictMono (ordinalOuterBlockMap a b Γ hshift hb) := by
  intro x y hxy
  change (a + 1) + x.val < (a + 1) + y.val
  change x.val < y.val at hxy
  exact add_lt_add_left hxy (a + 1)

theorem ordinalOuterBlockMap_range
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b < Γ) :
    range (ordinalOuterBlockMap a b Γ hshift hb) =
      {x : Iio Γ | a < x.val ∧ x.val ≤ b} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(lt_add_one a).trans_le (Ordinal.le_add_right _ _), ?_⟩
    change (a + 1) + x.val ≤ b
    simpa only [hshift] using add_le_add_left x.property (a + 1)
  · rintro ⟨hya, hyb⟩
    let x : Iic b := ⟨y.val - (a + 1), Ordinal.sub_le.mpr (hshift.symm ▸ hyb)⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact Ordinal.add_sub_cancel_of_le (Order.add_one_le_iff.mpr hya)

theorem ordinalOuterBlockMap_isOpenEmbedding
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b < Γ) :
    IsOpenEmbedding (ordinalOuterBlockMap a b Γ hshift hb) := by
  refine ⟨((ordinalOuterBlockMap a b Γ hshift hb).continuous.isClosedEmbedding
    (ordinalOuterBlockMap_strictMono a b Γ hshift hb).injective).isEmbedding, ?_⟩
  rw [ordinalOuterBlockMap_range]
  have he : {x : Iio Γ | a < x.val ∧ x.val ≤ b} =
      Subtype.val ⁻¹' (Ioi a ∩ Iio (Order.succ b)) := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_inter_iff, mem_Ioi, mem_Iio,
      Order.lt_succ_iff]
  rw [he]
  exact (isOpen_Ioi.inter isOpen_Iio).preimage continuous_subtype_val

theorem ordinalOuterBlockMap_isCompact_range
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b < Γ) :
    IsCompact (range (ordinalOuterBlockMap a b Γ hshift hb)) :=
  isCompact_range (ordinalOuterBlockMap a b Γ hshift hb).continuous

theorem ordinalOuterBlockMap_isClopen_range
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b < Γ) :
    IsClopen (range (ordinalOuterBlockMap a b Γ hshift hb)) :=
  ⟨(ordinalOuterBlockMap_isCompact_range a b Γ hshift hb).isClosed,
    (ordinalOuterBlockMap_isOpenEmbedding a b Γ hshift hb).isOpen_range⟩

theorem ordinal_initial_finite_power_block_shift
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c) {l m : ℕ} (hlm : l < m) :
    (c.ord ^ (l : Ordinal) + 1) + c.ord ^ (m : Ordinal) = c.ord ^ (m : Ordinal) := by
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)
  have hlt : c.ord ^ (l : Ordinal) < c.ord ^ (m : Ordinal) :=
    (Ordinal.opow_lt_opow_iff_right hκ).mpr (by exact_mod_cast hlm)
  have hlim : Order.IsSuccLimit (c.ord ^ (m : Ordinal)) :=
    Ordinal.isSuccLimit_opow_left (Cardinal.isSuccLimit_ord hc) (by exact_mod_cast (by omega : m ≠ 0))
  apply Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) _)
  simpa only [Ordinal.add_one_eq_succ] using hlim.succ_lt hlt

def ordinalRegularOmegaOuterBlock (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (l m : ℕ) (hlm : l < m) : C(Iic (c.ord ^ (m : Ordinal)), Iio (c.ord ^ Ordinal.omega0)) :=
  ordinalOuterBlockMap _ _ _ (ordinal_initial_finite_power_block_shift c hc hlm)
    ((Ordinal.opow_lt_opow_iff_right
      (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc))).mpr (Ordinal.nat_lt_omega0 m))

end Posets
