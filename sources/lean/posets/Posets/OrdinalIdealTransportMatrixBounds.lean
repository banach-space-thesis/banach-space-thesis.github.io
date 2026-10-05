import Posets.OrdinalIdealTransportDiagonalRows
import Posets.OrdinalIdealTransportCornerCutoffs

/-! Coding and predecessor bounds for a matrix indexed by a regular cardinal.
Only strictly earlier coordinates enter each supremum. -/
noncomputable section
namespace Posets
open JLMS
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

def ordinalMatrixCode {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c) :
    c.ord.toType × c.ord.toType ≃ Set.Iio c.ord := by
  have hm : Cardinal.mk (c.ord.toType × c.ord.toType) = Cardinal.mk c.ord.toType := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_toType, Cardinal.card_ord]
    exact Cardinal.mul_eq_self hu.le
  exact (Classical.choice (Cardinal.eq.mp hm)).trans (Ordinal.enumIsoToType c.ord).symm.toEquiv

def ordinalMatrixPredecessorBound {c : Cardinal.{0}}
    (b : c.ord.toType → c.ord.toType → Ordinal.{0}) (i : c.ord.toType) : Ordinal.{0} :=
  max (b i i) (⨆ j : Set.Iio i, max (b i j.val) (b j.val i))

theorem ordinalMatrixPredecessorBound_lt {c : Cardinal.{0}} (hc : c.IsRegular)
    (b : c.ord.toType → c.ord.toType → Ordinal.{0}) (hb : ∀ i j, b i j < c.ord)
    (i : c.ord.toType) : ordinalMatrixPredecessorBound b i < c.ord := by
  exact max_lt (hb i i) (Ordinal.iSup_lt_ord
    (by simpa only [hc.cof_eq] using Cardinal.mk_Iio_ord_toType i)
    (fun j => max_lt (hb i j.val) (hb j.val i)))

theorem ordinalMatrixPredecessorBound_diag {c : Cardinal.{0}}
    (b : c.ord.toType → c.ord.toType → Ordinal.{0}) (i : c.ord.toType) :
    b i i ≤ ordinalMatrixPredecessorBound b i := le_max_left _ _

theorem ordinalMatrixPredecessorBound_outgoing {c : Cardinal.{0}}
    (b : c.ord.toType → c.ord.toType → Ordinal.{0}) {i j : c.ord.toType} (hji : j < i) :
    b i j ≤ ordinalMatrixPredecessorBound b i := by
  exact (le_max_left _ _).trans ((Ordinal.le_iSup
    (fun j : Set.Iio i => max (b i j.val) (b j.val i)) ⟨j, hji⟩).trans (le_max_right _ _))

theorem ordinalMatrixPredecessorBound_incoming {c : Cardinal.{0}}
    (b : c.ord.toType → c.ord.toType → Ordinal.{0}) {i j : c.ord.toType} (hji : j < i) :
    b j i ≤ ordinalMatrixPredecessorBound b i := by
  exact (le_max_right _ _).trans ((Ordinal.le_iSup
    (fun j : Set.Iio i => max (b i j.val) (b j.val i)) ⟨j, hji⟩).trans (le_max_right _ _))

end Posets
