import ThesisCommon.Analysis.OrdinalBlockSum
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! The one-point compactification of a countable topological sum of
compact ordinal intervals is itself a compact ordinal interval. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

def ordinalBlockMap (a : ℕ → Ordinal.{u}) (n : ℕ) :
    C(OrdinalInterval (a n), OrdinalInterval (ordinalBlockSup a)) :=
  ⟨fun x => ⟨ordinalBlockStart a n + x.val, bot_le,
      (add_le_add_left x.property.2 _).trans (ordinalBlockEnd_lt_sup a n).le⟩,
    ((Ordinal.isNormal_add_right (ordinalBlockStart a n)).continuous.comp
      continuous_subtype_val).subtype_mk _⟩

theorem ordinalBlockMap_injective (a : ℕ → Ordinal.{u}) (n : ℕ) :
    Function.Injective (ordinalBlockMap a n) := by
  intro x y hxy
  apply Subtype.ext
  exact add_left_cancel (congrArg (fun z : OrdinalInterval (ordinalBlockSup a) => z.val) hxy)

theorem ordinalBlockMap_range (a : ℕ → Ordinal.{u}) (n : ℕ) :
    range (ordinalBlockMap a n) =
      {x | ordinalBlockStart a n ≤ x.val ∧ x.val ≤ ordinalBlockStart a n + a n} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Ordinal.le_add_right _ _, add_le_add_left x.property.2 _⟩
  · intro hz
    refine ⟨⟨z.val - ordinalBlockStart a n, bot_le, Ordinal.sub_le.mpr hz.2⟩, ?_⟩
    exact Subtype.ext (Ordinal.add_sub_cancel_of_le hz.1)

theorem ordinalBlockMap_isOpenEmbedding (a : ℕ → Ordinal.{u}) (n : ℕ) :
    IsOpenEmbedding (ordinalBlockMap a n) := by
  refine ⟨((ordinalBlockMap a n).continuous.isClosedEmbedding
    (ordinalBlockMap_injective a n)).isEmbedding, ?_⟩
  rw [ordinalBlockMap_range]
  have hleft : IsOpen (Ici (ordinalBlockStart a n)) := by
    rcases ordinalBlockStart_zero_or_succ a n with h | ⟨β, h⟩
    · simpa only [h, Ordinal.bot_eq_zero.symm, Ici_bot] using
        (isOpen_univ : IsOpen (univ : Set Ordinal.{u}))
    · rw [h, Order.Ici_succ]
      exact isOpen_Ioi
  have hright : IsOpen (Iic (ordinalBlockStart a n + a n)) := by
    rw [← Order.Iio_succ]
    exact isOpen_Iio
  exact (hleft.inter hright).preimage continuous_subtype_val

def ordinalBlockUnion (a : ℕ → Ordinal.{u}) :
    (Σ n : ℕ, OrdinalInterval (a n)) → OrdinalInterval (ordinalBlockSup a) :=
  fun z => ordinalBlockMap a z.1 z.2

theorem ordinalBlockUnion_injective (a : ℕ → Ordinal.{u}) :
    Function.Injective (ordinalBlockUnion a) := by
  rintro ⟨n, x⟩ ⟨m, y⟩ hxy
  have hv : ordinalBlockStart a n + x.val = ordinalBlockStart a m + y.val :=
    congrArg (fun z : OrdinalInterval (ordinalBlockSup a) => z.val) hxy
  have hnm : n = m := by
    rcases lt_trichotomy n m with h | h | h
    · have hlt := (add_le_add_left x.property.2 (ordinalBlockStart a n)).trans_lt
        ((ordinalBlockEnd_lt_start h).trans_le (Ordinal.le_add_right _ y.val))
      exact False.elim ((ne_of_lt hlt) hv)
    · exact h
    · have hlt := (add_le_add_left y.property.2 (ordinalBlockStart a m)).trans_lt
        ((ordinalBlockEnd_lt_start h).trans_le (Ordinal.le_add_right _ x.val))
      exact False.elim ((ne_of_lt hlt) hv.symm)
  subst m
  congr 1
  exact ordinalBlockMap_injective a n hxy

theorem ordinalBlockUnion_isOpenEmbedding (a : ℕ → Ordinal.{u}) :
    IsOpenEmbedding (ordinalBlockUnion a) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_sigma fun n => (ordinalBlockMap a n).continuous
  · exact ordinalBlockUnion_injective a
  · exact isOpenMap_sigma.mpr fun n => (ordinalBlockMap_isOpenEmbedding a n).isOpenMap

def ordinalBlockTop (a : ℕ → Ordinal.{u}) : OrdinalInterval (ordinalBlockSup a) :=
  ⟨ordinalBlockSup a, bot_le, le_rfl⟩

theorem ordinalBlockUnion_range (a : ℕ → Ordinal.{u}) :
    range (ordinalBlockUnion a) = {ordinalBlockTop a}ᶜ := by
  ext z
  constructor
  · rintro ⟨⟨n, x⟩, rfl⟩ h
    have hv := congrArg (fun z : OrdinalInterval (ordinalBlockSup a) => z.val) h
    have hlt : ordinalBlockStart a n + x.val < ordinalBlockSup a :=
      (add_le_add_left x.property.2 _).trans_lt (ordinalBlockEnd_lt_sup a n)
    exact (ne_of_lt hlt) hv
  · intro hz
    have hlt : z.val < ordinalBlockSup a := by
      by_contra h
      exact hz (Subtype.ext (le_antisymm z.property.2 (le_of_not_gt h)))
    obtain ⟨n, hlo, hhi⟩ := ordinalBlock_covers hlt
    have hzrange : z ∈ range (ordinalBlockMap a n) := by
      rw [ordinalBlockMap_range]
      exact ⟨hlo, hhi⟩
    obtain ⟨x, hx⟩ := hzrange
    exact ⟨⟨n, x⟩, hx⟩

/-- Explicit ordinal gluing for a sequence of compact nonempty ordinal blocks. -/
def ordinalOnePointSumHomeomorph (a : ℕ → Ordinal.{u}) :
    OnePoint (Σ n : ℕ, OrdinalInterval (a n)) ≃ₜ OrdinalInterval (ordinalBlockSup a) :=
  OnePoint.equivOfIsEmbeddingOfRangeEq (ordinalBlockTop a) (ordinalBlockUnion a)
    (ordinalBlockUnion_isOpenEmbedding a).isEmbedding (ordinalBlockUnion_range a)

end ThesisCommon
