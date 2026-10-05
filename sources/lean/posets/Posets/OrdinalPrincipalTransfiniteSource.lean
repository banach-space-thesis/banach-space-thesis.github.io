import Posets.OrdinalPrincipalTransfiniteSequence
import JLMS.OrdinalSpaceBlocksTopology

/-! Actual open source copies in genuine transfinite consecutive blocks.
Their ranges stop at the principal endpoint, before the extra successor
point which is the right anchor of the ambient block. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets

local instance transfiniteSourceCompactIic (b : Ordinal.{u}) : CompactSpace (Iic b) := by
  apply isCompact_iff_compactSpace.mp
  have he : Icc (0 : Ordinal.{u}) b = Iic b := by ext x; simp
  rw [← he]
  exact isCompact_Icc

def ordinalOuterBlockIntervalMap (a b Γ : Ordinal.{u})
    (hshift : (a + 1) + b = b) (hb : b ≤ Γ) : C(Iic b, JLMS.OrdinalInterval Γ) :=
  ⟨fun x => ⟨(a + 1) + x.val, Ordinal.zero_le _, by
      apply le_trans _ hb
      simpa only [hshift] using add_le_add_left x.property (a + 1)⟩,
    ((Ordinal.isNormal_add_right (a + 1)).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem ordinalOuterBlockIntervalMap_apply
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b ≤ Γ) (x : Iic b) :
    (ordinalOuterBlockIntervalMap a b Γ hshift hb x).val = (a + 1) + x.val := rfl

theorem ordinalOuterBlockIntervalMap_strictMono
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b ≤ Γ) :
    StrictMono (ordinalOuterBlockIntervalMap a b Γ hshift hb) := by
  intro x y hxy
  change (a + 1) + x.val < (a + 1) + y.val
  change x.val < y.val at hxy
  exact add_lt_add_left hxy (a + 1)

theorem ordinalOuterBlockIntervalMap_range
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b ≤ Γ) :
    range (ordinalOuterBlockIntervalMap a b Γ hshift hb) =
      {x : JLMS.OrdinalInterval Γ | a < x.val ∧ x.val ≤ b} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(lt_add_one a).trans_le (Ordinal.le_add_right _ _), ?_⟩
    change (a + 1) + x.val ≤ b
    simpa only [hshift] using add_le_add_left x.property (a + 1)
  · rintro ⟨hya, hyb⟩
    let x : Iic b := ⟨y.val - (a + 1), Ordinal.sub_le.mpr (hshift.symm ▸ hyb)⟩
    exact ⟨x, Subtype.ext (Ordinal.add_sub_cancel_of_le (Order.add_one_le_iff.mpr hya))⟩

theorem ordinalOuterBlockIntervalMap_isOpenEmbedding
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b ≤ Γ) :
    IsOpenEmbedding (ordinalOuterBlockIntervalMap a b Γ hshift hb) := by
  refine ⟨((ordinalOuterBlockIntervalMap a b Γ hshift hb).continuous.isClosedEmbedding
    (ordinalOuterBlockIntervalMap_strictMono a b Γ hshift hb).injective).isEmbedding, ?_⟩
  rw [ordinalOuterBlockIntervalMap_range]
  have he : {x : JLMS.OrdinalInterval Γ | a < x.val ∧ x.val ≤ b} =
      Subtype.val ⁻¹' (Ioi a ∩ Iio (succ b)) := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_inter_iff, mem_Ioi, mem_Iio, lt_succ_iff]
  rw [he]
  exact (isOpen_Ioi.inter isOpen_Iio).preimage continuous_subtype_val

theorem ordinalOuterBlockIntervalMap_isCompact_range
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b ≤ Γ) :
    IsCompact (range (ordinalOuterBlockIntervalMap a b Γ hshift hb)) :=
  isCompact_range (ordinalOuterBlockIntervalMap a b Γ hshift hb).continuous

theorem ordinalOuterBlockIntervalMap_isClopen_range
    (a b Γ : Ordinal.{u}) (hshift : (a + 1) + b = b) (hb : b ≤ Γ) :
    IsClopen (range (ordinalOuterBlockIntervalMap a b Γ hshift hb)) :=
  ⟨(ordinalOuterBlockIntervalMap_isCompact_range a b Γ hshift hb).isClosed,
    (ordinalOuterBlockIntervalMap_isOpenEmbedding a b Γ hshift hb).isOpen_range⟩

namespace OrdinalPrincipalTransfiniteSequence
variable {Λ Γ : Ordinal.{u}} (P : OrdinalPrincipalTransfiniteSequence Λ Γ)

theorem endpoint_infinite (i : Iio Λ) : Ordinal.omega0 ≤ P.endpoint i :=
  (P.infinite.trans P.head_large.le).trans (P.strictMono.monotone (Ordinal.zero_le i.val))

theorem endpoint_isSuccLimit (i : Iio Λ) : IsSuccLimit (P.endpoint i) :=
  Ordinal.isSuccLimit_of_principal_add
    (Ordinal.one_lt_omega0.trans_le (P.endpoint_infinite i)) (P.principal i)

theorem source_shift (i : Iio Λ) :
    (P.boundary i.val + 1) + P.endpoint i = P.endpoint i := by
  apply Ordinal.principal_add_iff_add_left_eq_self.mp (P.principal i)
  simpa only [Ordinal.add_one_eq_succ] using
    (P.endpoint_isSuccLimit i).succ_lt (P.boundary_lt i)

def sourceEmbedding (i : Iio Λ) : C(Iic (P.endpoint i), JLMS.OrdinalInterval Γ) :=
  ordinalOuterBlockIntervalMap _ _ _ (P.source_shift i) (P.bound i).le

theorem sourceEmbedding_isOpen (i : Iio Λ) : IsOpenEmbedding (P.sourceEmbedding i) :=
  ordinalOuterBlockIntervalMap_isOpenEmbedding _ _ _ _ _

theorem sourceEmbedding_range (i : Iio Λ) :
    range (P.sourceEmbedding i) =
      {x : JLMS.OrdinalInterval Γ | P.boundary i.val < x.val ∧ x.val ≤ P.endpoint i} :=
  ordinalOuterBlockIntervalMap_range _ _ _ _ _

theorem sourceEmbedding_range_isCompact (i : Iio Λ) :
    IsCompact (range (P.sourceEmbedding i)) :=
  ordinalOuterBlockIntervalMap_isCompact_range _ _ _ _ _

theorem sourceEmbedding_range_isClopen (i : Iio Λ) :
    IsClopen (range (P.sourceEmbedding i)) :=
  ordinalOuterBlockIntervalMap_isClopen_range _ _ _ _ _

theorem sourceEmbedding_range_subset_block (i : Iio Λ) :
    range (P.sourceEmbedding i) ⊆ JLMS.ordinalSpaceBlockSet P.blockMap i := by
  intro x hx
  rw [P.sourceEmbedding_range] at hx
  change P.boundary i.val < x.val ∧ x.val ≤ P.boundary (succ i.val)
  rw [P.boundary_succ]
  exact ⟨hx.1, hx.2.trans (Order.le_succ _)⟩

theorem sourceEmbedding_range_disjoint_boundary (i : Iio Λ) :
    Disjoint (range (P.sourceEmbedding i)) (range P.blockMap) := by
  apply disjoint_left.mpr
  rintro x hx ⟨η, rfl⟩
  have hη : η.val = succ i.val :=
    (JLMS.ordinalSpaceBlock_range_mem_iff P.blockMap P.blockMap_strictMono i η).mp
      (P.sourceEmbedding_range_subset_block i hx)
  rw [P.sourceEmbedding_range] at hx
  have hle : P.boundary η.val ≤ P.endpoint i := hx.2
  rw [hη, P.boundary_succ] at hle
  exact (Order.lt_succ (P.endpoint i)).not_ge hle

theorem sourceEmbedding_anchor_not_mem_range (i : Iio Λ) :
    P.blockMap ⟨succ i.val, Ordinal.zero_le _, succ_le_of_lt i.property⟩ ∉
      range (P.sourceEmbedding i) := by
  intro hx
  exact disjoint_left.mp (P.sourceEmbedding_range_disjoint_boundary i) hx (mem_range_self _)

theorem sourceEmbedding_ranges_disjoint :
    Pairwise (fun i j => Disjoint (range (P.sourceEmbedding i)) (range (P.sourceEmbedding j))) := by
  intro i j hij
  exact (JLMS.ordinalSpaceBlocks_pairwiseDisjoint P.blockMap P.blockMap_strictMono hij).mono
    (P.sourceEmbedding_range_subset_block i) (P.sourceEmbedding_range_subset_block j)

end OrdinalPrincipalTransfiniteSequence
end Posets



