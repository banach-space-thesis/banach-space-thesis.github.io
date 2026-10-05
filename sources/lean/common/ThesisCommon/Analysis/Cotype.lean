import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi

/-! Rademacher cotype in the q-moment convention used in the UPFP paper.
The finite uniform expectation is expanded as a sum over all 2^n sign vectors.
Reference for this convention: Mendel--Naor, Metric Cotype, Introduction (2).
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

variable (X : Type*) [NormedAddCommGroup X]

/-- Uniform Rademacher cotype q inequality, with constant C. The qth powers
are real powers. Finiteness of q is automatic since q : ℝ. -/
def HasRademacherCotype (q C : ℝ) : Prop :=
  2 ≤ q ∧ 1 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → X),
    (∑ i, ‖x i‖ ^ q) ≤
      C ^ q * ((2 : ℝ) ^ n)⁻¹ *
        ∑ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ^ q

/-- There are one finite exponent and one constant valid for every finite family. -/
def HasFiniteCotype : Prop := ∃ q C : ℝ, HasRademacherCotype X q C

end ThesisCommon
