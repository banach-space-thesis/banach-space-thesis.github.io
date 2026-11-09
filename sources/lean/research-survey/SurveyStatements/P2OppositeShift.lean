import SurveyStatements.P2CardinalTrap
import Mathlib.Algebra.Algebra.Opposite

/-! Opposite shifts provide the first proof's bounded-row matrix units. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators
open MulOpposite

namespace SurveyStatements.P2
universe u
variable (Γ : Type u)
local instance : DecidableEq Γ := Classical.decEq Γ

def oppositeShiftBanachAlgebra : ComplexBanachAlgebra where
  Carrier := (ShiftQuotient Γ)ᵐᵒᵖ

theorem oppositeShiftQuotient_simple (J : TwoSidedIdeal (ShiftQuotient Γ)ᵐᵒᵖ) :
    J = ⊥ ∨ J = ⊤ := by
  rcases shiftQuotient_simple Γ J.unop with h | h
  · left
    apply SetLike.ext
    intro x
    have hx := SetLike.ext_iff.mp h (unop x)
    simpa using hx
  · right
    apply SetLike.ext
    intro x
    have hx := SetLike.ext_iff.mp h (unop x)
    simpa using hx

/-- Reversing multiplication turns the disjoint-column estimate into a row estimate. -/
def oppositeMatrixUnit (a b : Γ) : (ShiftQuotient Γ)ᵐᵒᵖ :=
  op (quotientPrefix Γ b * quotientRemoval Γ a)

theorem oppositeMatrixUnit_mul (a b c d : Γ) :
    oppositeMatrixUnit Γ a b * oppositeMatrixUnit Γ c d =
      if b = c then oppositeMatrixUnit Γ a d else 0 := by
  classical
  apply unop_injective
  simp only [oppositeMatrixUnit, unop_mul, unop_op]
  have h : (quotientPrefix Γ d * quotientRemoval Γ c) *
      (quotientPrefix Γ b * quotientRemoval Γ a) =
      quotientPrefix Γ d * (quotientRemoval Γ c * quotientPrefix Γ b) *
        quotientRemoval Γ a := by simp only [mul_assoc]
  rw [h, quotientRemoval_mul_quotientPrefix]
  by_cases hbc : b = c <;> simp [hbc, eq_comm]

theorem oppositeMatrixUnit_diagonal_ne_zero (a : Γ) :
    oppositeMatrixUnit Γ a a ≠ 0 := by
  intro hzero
  have hproduct : quotientPrefix Γ a * quotientRemoval Γ a = 0 :=
    congrArg unop hzero
  have hleft : quotientRemoval Γ a * quotientPrefix Γ a = 1 := by
    simp [quotientRemoval_mul_quotientPrefix]
  have h : (1 : ShiftQuotient Γ) = 0 := by
    calc
      1 = quotientRemoval Γ a * (quotientPrefix Γ a * quotientRemoval Γ a) *
          quotientPrefix Γ a := by simp only [← mul_assoc, hleft, one_mul]
      _ = 0 := by rw [hproduct]; simp
  exact one_ne_zero h

theorem norm_oppositeMatrixUnit_le (a b : Γ) : ‖oppositeMatrixUnit Γ a b‖ ≤ 1 := by
  change ‖quotientPrefix Γ b * quotientRemoval Γ a‖ ≤ 1
  calc
    _ ≤ ‖quotientPrefix Γ b‖ * ‖quotientRemoval Γ a‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_quotientPrefix_le Γ b)
      (norm_quotientRemoval_le Γ a) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

theorem norm_sum_oppositeMatrixUnit_row_le (a : Γ) (F : Finset Γ)
    (z : Γ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hz : ∀ b ∈ F, ‖z b‖ ≤ C) :
    ‖∑ b ∈ F, z b • oppositeMatrixUnit Γ a b‖ ≤ C := by
  have hsum : ∑ b ∈ F, z b • oppositeMatrixUnit Γ a b =
      op ((∑ b ∈ F, z b • quotientPrefix Γ b) * quotientRemoval Γ a) := by
    simp only [oppositeMatrixUnit, ← op_smul, ← Finset.op_sum, Finset.sum_mul, smul_mul_assoc]
  rw [hsum, norm_op]
  calc
    _ ≤ ‖∑ b ∈ F, z b • quotientPrefix Γ b‖ * ‖quotientRemoval Γ a‖ := norm_mul_le _ _
    _ ≤ C * 1 := mul_le_mul (norm_sum_quotientPrefix_le Γ F z C hC hz)
      (norm_quotientRemoval_le Γ a) (norm_nonneg _) hC
    _ = C := mul_one _

theorem bethOmega_le_mk_oppositeShiftQuotient :
    bethOmega ≤ Cardinal.mk (ShiftQuotient LargeAlphabet)ᵐᵒᵖ := by
  exact bethOmega_le_mk_shiftQuotient.trans_eq (Cardinal.mk_congr opEquiv)

/-- The countable distinct letters used to extract the obstruction. -/
def countableLetters : ℕ ↪ LargeAlphabet :=
  Classical.choice ((Cardinal.le_def ℕ LargeAlphabet).mp (by
    rw [Cardinal.mk_nat, mk_largeAlphabet]
    exact Cardinal.aleph0_le_continuum.trans continuum_lt_bethOmega.le))

def countableOppositeMatrixUnit (i j : ℕ) : (ShiftQuotient LargeAlphabet)ᵐᵒᵖ :=
  oppositeMatrixUnit LargeAlphabet (countableLetters i) (countableLetters j)

theorem countableOppositeMatrixUnit_mul (i j k l : ℕ) :
    countableOppositeMatrixUnit i j * countableOppositeMatrixUnit k l =
      if j = k then countableOppositeMatrixUnit i l else 0 := by
  simpa [countableOppositeMatrixUnit, countableLetters.injective.eq_iff] using
    oppositeMatrixUnit_mul LargeAlphabet (countableLetters i) (countableLetters j)
      (countableLetters k) (countableLetters l)

theorem countableOppositeMatrixUnit_diagonal_ne_zero (i : ℕ) :
    countableOppositeMatrixUnit i i ≠ 0 :=
  oppositeMatrixUnit_diagonal_ne_zero LargeAlphabet _

theorem norm_countableOppositeMatrixUnit_le (i j : ℕ) :
    ‖countableOppositeMatrixUnit i j‖ ≤ 1 := norm_oppositeMatrixUnit_le LargeAlphabet _ _

theorem norm_sum_countableOppositeMatrixUnit_row_le (i : ℕ) (F : Finset ℕ)
    (z : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hz : ∀ j ∈ F, ‖z j‖ ≤ C) :
    ‖∑ j ∈ F, z j • countableOppositeMatrixUnit i j‖ ≤ C := by
  classical
  let z' : LargeAlphabet → ℂ := fun a => z (Function.invFun countableLetters a)
  have hcoeff : ∀ j, z' (countableLetters j) = z j := fun j =>
    congrArg z (Function.leftInverse_invFun countableLetters.injective j)
  have hz' : ∀ a ∈ F.map countableLetters, ‖z' a‖ ≤ C := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
    simpa only [hcoeff] using hz j hj
  have h := norm_sum_oppositeMatrixUnit_row_le LargeAlphabet (countableLetters i)
    (F.map countableLetters) z' C hC hz'
  simpa only [Finset.sum_map, hcoeff,
    countableOppositeMatrixUnit] using h

end SurveyStatements.P2
