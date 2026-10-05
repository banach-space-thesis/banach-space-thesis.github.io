import ThesisCommon.Analysis.ALFragmentBasic
import Mathlib.Order.LatticeIntervals
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.ENNReal.Real

/-! The Boolean algebra of fragments of a positive vector, realized as the
complemented elements of its order interval. AL norm additivity gives its
finite, strictly positive Boolean content. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E]
  [Lattice E] [IsOrderedAddMonoid E]

local instance : DistribLattice E := AddCommGroup.toDistribLattice E

private instance intervalDistrib (e : E) : DistribLattice (Icc (0:E) e) :=
  Subtype.val_injective.distribLattice _ (fun _ _ => rfl) (fun _ _ => rfl)

def PositiveFragmentAlgebra (e : E) [Fact (0 ≤ e)] := Complementeds (Icc (0:E) e)

instance positiveFragmentDistrib (e : E) [Fact (0 ≤ e)] :
    DistribLattice (PositiveFragmentAlgebra e) :=
  inferInstanceAs (DistribLattice (Complementeds (Icc (0:E) e)))

instance positiveFragmentBounded (e : E) [Fact (0 ≤ e)] :
    BoundedOrder (PositiveFragmentAlgebra e) :=
  inferInstanceAs (BoundedOrder (Complementeds (Icc (0:E) e)))

instance positiveFragmentComplemented (e : E) [Fact (0 ≤ e)] :
    ComplementedLattice (PositiveFragmentAlgebra e) :=
  inferInstanceAs (ComplementedLattice (Complementeds (Icc (0:E) e)))

instance positiveFragmentBoolean (e : E) [Fact (0 ≤ e)] :
    BooleanAlgebra (PositiveFragmentAlgebra e) := DistribLattice.booleanAlgebraOfComplemented _

def positiveFragmentValue {e : E} [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) : E := a.val.val

omit [IsOrderedAddMonoid E] in
theorem positiveFragmentValue_injective (e : E) [Fact (0 ≤ e)] :
    Function.Injective (positiveFragmentValue (e := e)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

omit [IsOrderedAddMonoid E] in
theorem positiveFragmentValue_nonneg {e : E} [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) :
    0 ≤ positiveFragmentValue a := a.val.property.1

omit [IsOrderedAddMonoid E] in
theorem positiveFragmentValue_le {e : E} [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) :
    positiveFragmentValue a ≤ e := a.val.property.2

@[simp] theorem positiveFragmentValue_bot (e : E) [Fact (0 ≤ e)] :
    positiveFragmentValue (⊥ : PositiveFragmentAlgebra e) = 0 := rfl

@[simp] theorem positiveFragmentValue_top (e : E) [Fact (0 ≤ e)] :
    positiveFragmentValue (⊤ : PositiveFragmentAlgebra e) = e := rfl

@[simp] theorem positiveFragmentValue_sup {e : E} [Fact (0 ≤ e)]
    (a b : PositiveFragmentAlgebra e) :
    positiveFragmentValue (a ⊔ b) = positiveFragmentValue a ⊔ positiveFragmentValue b := rfl

@[simp] theorem positiveFragmentValue_inf {e : E} [Fact (0 ≤ e)]
    (a b : PositiveFragmentAlgebra e) :
    positiveFragmentValue (a ⊓ b) = positiveFragmentValue a ⊓ positiveFragmentValue b := rfl

theorem positiveFragmentValue_compl {e : E} [Fact (0 ≤ e)]
    (a : PositiveFragmentAlgebra e) : positiveFragmentValue aᶜ = e-positiveFragmentValue a := by
  have h0 := congrArg positiveFragmentValue (inf_compl_eq_bot (a := a))
  have h1 := congrArg positiveFragmentValue (sup_compl_eq_top (x := a))
  simp only [positiveFragmentValue_inf, positiveFragmentValue_sup,
    positiveFragmentValue_bot, positiveFragmentValue_top] at h0 h1
  have h := inf_add_sup (positiveFragmentValue a) (positiveFragmentValue aᶜ)
  rw [h0, h1, zero_add] at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using h.symm

theorem positiveFragmentValue_isFragment {e : E} [Fact (0 ≤ e)]
    (a : PositiveFragmentAlgebra e) : IsPositiveFragment (positiveFragmentValue a) e := by
  refine ⟨positiveFragmentValue_nonneg a, positiveFragmentValue_le a, ?_⟩
  rw [← positiveFragmentValue_compl, ← positiveFragmentValue_inf, inf_compl_eq_bot,
    positiveFragmentValue_bot]

def positiveFragmentOf {e a : E} [Fact (0 ≤ e)] (ha : IsPositiveFragment a e) :
    PositiveFragmentAlgebra e :=
  ⟨⟨a, ha.1, ha.2.1⟩, ⟨⟨e-a, sub_nonneg.mpr ha.2.1, sub_le_self e ha.1⟩,
    Set.Icc.isCompl_iff.mpr ⟨ha.2.2, by
      have h := inf_add_sup a (e-a)
      rw [ha.2.2, zero_add, add_sub_cancel] at h
      exact h⟩⟩⟩

@[simp] theorem positiveFragmentValue_of {e a : E} [Fact (0 ≤ e)]
    (ha : IsPositiveFragment a e) : positiveFragmentValue (positiveFragmentOf ha) = a := rfl

def positiveFragmentMass {e : E} [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) : ENNReal :=
  ENNReal.ofReal ‖positiveFragmentValue a‖

@[simp] theorem positiveFragmentMass_bot (e : E) [Fact (0 ≤ e)] :
    positiveFragmentMass (⊥ : PositiveFragmentAlgebra e) = 0 := by
  simp [positiveFragmentMass]

omit [IsOrderedAddMonoid E] in
theorem positiveFragmentMass_ne_top {e : E} [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) :
    positiveFragmentMass a ≠ ⊤ := ENNReal.ofReal_ne_top

theorem positiveFragmentMass_eq_zero_iff {e : E} [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) :
    positiveFragmentMass a = 0 ↔ a = ⊥ := by
  rw [positiveFragmentMass, ENNReal.ofReal_eq_zero, norm_le_zero_iff]
  exact ⟨fun h => positiveFragmentValue_injective e (h.trans (positiveFragmentValue_bot e).symm),
    fun h => h ▸ positiveFragmentValue_bot e⟩

theorem positiveFragmentMass_sup_of_disjoint
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    {e : E} [Fact (0 ≤ e)] (a b : PositiveFragmentAlgebra e) (hab : Disjoint a b) :
    positiveFragmentMass (a ⊔ b) = positiveFragmentMass a + positiveFragmentMass b := by
  have h0 := congrArg positiveFragmentValue hab.eq_bot
  simp only [positiveFragmentValue_inf, positiveFragmentValue_bot] at h0
  have hsum := inf_add_sup (positiveFragmentValue a) (positiveFragmentValue b)
  rw [h0, zero_add] at hsum
  simp only [positiveFragmentMass, positiveFragmentValue_sup, hsum,
    hAL _ _ (positiveFragmentValue_nonneg a) (positiveFragmentValue_nonneg b)]
  exact ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)

end ThesisCommon
