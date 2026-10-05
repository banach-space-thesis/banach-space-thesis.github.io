import JLMS.Definitions
import Mathlib.SetTheory.Ordinal.Topology

/-!
# Scatteredness of arbitrary ordinal intervals

Every nonempty ordinal set has a least element. The open initial interval
ending at its successor isolates that element. Passing to subspaces gives
scatteredness of [0,α], with no countability restriction on α.
-/

noncomputable section
namespace JLMS
universe u

theorem scattered_ordinal : IsScattered Ordinal.{u} := by
  intro s hs
  obtain ⟨x, hx, hmin⟩ := wellFounded_lt.has_min s hs
  refine ⟨x, hx, Set.Iio (Order.succ x), isOpen_Iio, ?_⟩
  ext y
  constructor
  · intro hy
    apply Set.mem_singleton_iff.mpr
    have hyx : y ≤ x := Order.lt_succ_iff.mp hy.2
    have hxy : x ≤ y := le_of_not_gt (hmin y hy.1)
    exact le_antisymm hyx hxy
  · intro hy
    subst y
    exact ⟨hx, Order.lt_succ x⟩

theorem scattered_subtype {K : Type*} [TopologicalSpace K] (hK : IsScattered K) (S : Set K) :
    IsScattered S := by
  intro s hs
  obtain ⟨x, hx, U, hU, hi⟩ := hK (Subtype.val '' s) (hs.image _)
  obtain ⟨y, hys, rfl⟩ := hx
  refine ⟨y, hys, Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, ?_⟩
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    exact Set.mem_singleton_iff.mp (hi ▸ ⟨⟨z, hz.1, rfl⟩, hz.2⟩)
  · intro hz
    subst z
    refine ⟨hys, ?_⟩
    exact (show y.val ∈ Subtype.val '' s ∩ U from hi.symm ▸ Set.mem_singleton y.val).2

theorem scattered_ordinalInterval (α : Ordinal.{u}) : IsScattered (OrdinalInterval α) :=
  scattered_subtype scattered_ordinal _

end JLMS
