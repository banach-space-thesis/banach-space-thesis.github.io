import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.GroupTheory.OrderOfElement

/-!
# Actual repeated cubical maps and finite-order null-homotopies

The operation below concatenates continuous generalized loops, not abstract
group elements. Its class is the corresponding power in Mathlib's homotopy
group. A finite-order class therefore supplies an actual homotopy, fixed on
the cube boundary, from a positive repetition to the constant map.

This is the repetition algebra for a future clutching construction. Finiteness
of even homotopy groups of compact connected matrix groups is not proved or
postulated here. Nor is this cubical result labelled a sphere degree theorem.
-/

noncomputable section

namespace BanachIsometric

open scoped Topology Topology.Homotopy

variable {N X : Type*} [DecidableEq N] [TopologicalSpace X] {x : X}

/-- The actual quotient class, with its homotopy-group type retained during
elaboration of group operations. -/
def genLoopClass (p : GenLoop N X x) : HomotopyGroup N X x := Quotient.mk' p

/-- Concatenate a based cubical map a specified number of times along one
coordinate, preserving the actual boundary condition. -/
def repeatGenLoop (i : N) (p : GenLoop N X x) : ℕ → GenLoop N X x
  | 0 => GenLoop.const
  | d + 1 => GenLoop.transAt i (repeatGenLoop i p d) p

@[simp] theorem repeatGenLoop_zero (i : N) (p : GenLoop N X x) :
    repeatGenLoop i p 0 = GenLoop.const := rfl

@[simp] theorem repeatGenLoop_succ (i : N) (p : GenLoop N X x) (d : ℕ) :
    repeatGenLoop i p (d + 1) = GenLoop.transAt i (repeatGenLoop i p d) p := rfl

theorem repeatGenLoop_class [Nonempty N] (i : N) (p : GenLoop N X x) (d : ℕ) :
    genLoopClass (repeatGenLoop i p d) = genLoopClass p ^ d := by
  induction d with
  | zero => exact (HomotopyGroup.one_def).symm
  | succ d ih =>
      change (⟦GenLoop.transAt i (repeatGenLoop i p d) p⟧ : HomotopyGroup N X x) = _
      rw [← HomotopyGroup.mul_spec]
      change genLoopClass p * genLoopClass (repeatGenLoop i p d) = genLoopClass p ^ (d + 1)
      rw [ih, pow_succ']

/-- The algebraic finite-order assertion produces an actual relative
null-homotopy of a positive concatenation of the supplied continuous map. -/
theorem exists_positive_repeatGenLoop_nullhomotopic_of_finiteOrder [Nonempty N]
    (i : N) (p : GenLoop N X x)
    (hp : IsOfFinOrder (genLoopClass p)) :
    ∃ d : ℕ, 0 < d ∧ GenLoop.Homotopic (repeatGenLoop i p d) GenLoop.const := by
  obtain ⟨d, hd, hpow⟩ := hp.exists_pow_eq_one
  have hq : genLoopClass (repeatGenLoop i p d) = genLoopClass GenLoop.const := by
    rw [repeatGenLoop_class, hpow]
    exact HomotopyGroup.one_def
  exact ⟨d, hd, @Quotient.exact (GenLoop N X x)
    (GenLoop.Homotopic.setoid N x) _ _ hq⟩

/-- If the actual homotopy group is finite, the repetition above is
null-homotopic for some positive repetition number. This is an explicit
conditional reduction, not a proof of any Lie-group homotopy finiteness. -/
theorem exists_positive_repeatGenLoop_nullhomotopic_of_finite [Nonempty N]
    [Finite (HomotopyGroup N X x)] (i : N) (p : GenLoop N X x) :
    ∃ d : ℕ, 0 < d ∧ GenLoop.Homotopic (repeatGenLoop i p d) GenLoop.const :=
  exists_positive_repeatGenLoop_nullhomotopic_of_finiteOrder i p (isOfFinOrder_of_finite _)

end BanachIsometric
