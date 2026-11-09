import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Group.Lattice

/-!
# Equivalent real lattice norms

This predicate allows BOTH an arbitrary lattice order AND an equivalent norm.
It keeps the original vector-space addition and real scalar multiplication.
It does not merely ask whether the current norm is a lattice norm.

On a complete space the positive lower bound makes the seminorm a genuine
complete norm. The intended meaning is therefore existence of an equivalent
Banach-lattice norm. LatticeBridge.lean verifies the implication from a bounded
linear isomorphism to an arbitrary BanLat Banach lattice (in any universe).
-/

noncomputable section
universe u

namespace PL1

/-- An arbitrary compatible real lattice order and solid norm equivalent to the
original norm. Positivity of a,b is explicit, including for the zero space. -/
def HasEquivalentRealLatticeNorm (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Prop :=
  ∃ latticeOrder : Lattice E,
    letI := latticeOrder
    IsOrderedAddMonoid E ∧ PosSMulMono ℝ E ∧
      ∃ p : Seminorm ℝ E,
        (∀ x y : E, |x| ≤ |y| → p x ≤ p y) ∧
        ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
          ∀ x : E, a * ‖x‖ ≤ p x ∧ p x ≤ b * ‖x‖

end PL1
