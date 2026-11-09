import SurveyStatements.P2QuotientAlgebra
import SurveyStatements.P2Cardinals
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! The actual simple quotient and the separated family surviving in it. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace SurveyStatements.P2
universe u
variable (Γ : Type u)
local instance : DecidableEq Γ := Classical.decEq Γ

/-- The source's quotient, with its complete normed algebra structure. -/
def quotientShiftBanachAlgebra : ComplexBanachAlgebra where
  Carrier := ShiftQuotient Γ

/-- Maximality gives algebraic simplicity, hence also topological simplicity. -/
theorem shiftQuotient_simple (J : TwoSidedIdeal (ShiftQuotient Γ)) :
    J = ⊥ ∨ J = ⊤ :=
  idealQuotient_simple (shiftMaximalIdeal Γ) (shiftMaximalIdeal_isCoatom Γ) J

def quotientPrefix (a : Γ) : ShiftQuotient Γ :=
  idealQuotientMap (shiftMaximalIdeal Γ) (algebraPrefix Γ a)

def quotientRemoval (a : Γ) : ShiftQuotient Γ :=
  idealQuotientMap (shiftMaximalIdeal Γ) (algebraRemoval Γ a)

theorem quotientRemoval_mul_quotientPrefix (a b : Γ) :
    quotientRemoval Γ a * quotientPrefix Γ b = if a = b then 1 else 0 := by
  classical
  rw [quotientRemoval, quotientPrefix, ← idealQuotientMap_mul,
    algebraRemoval_mul_algebraPrefix]
  split_ifs <;> simp

theorem norm_quotientPrefix_le (a : Γ) : ‖quotientPrefix Γ a‖ ≤ 1 := by
  exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_algebraPrefix Γ a).le

theorem norm_quotientRemoval_le (a : Γ) : ‖quotientRemoval Γ a‖ ≤ 1 := by
  exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_algebraRemoval Γ a).le

theorem norm_sum_quotientPrefix_le (F : Finset Γ) (a : Γ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ b ∈ F, ‖a b‖ ≤ C) :
    ‖∑ b ∈ F, a b • quotientPrefix Γ b‖ ≤ C := by
  have hmap : ∑ b ∈ F, a b • quotientPrefix Γ b =
      idealQuotientMap (shiftMaximalIdeal Γ) (∑ b ∈ F, a b • algebraPrefix Γ b) := by
    simp only [quotientPrefix, map_sum, map_smul]
  rw [hmap]
  exact (Submodule.Quotient.norm_mk_le _ _).trans
    (norm_sum_algebraPrefix_le Γ F a C hC ha)

/-- Distinct letters survive every proper quotient with distance at least one. -/
theorem one_le_dist_quotientPrefix {a b : Γ} (hab : a ≠ b) :
    1 ≤ dist (quotientPrefix Γ a) (quotientPrefix Γ b) := by
  have hrelation : quotientRemoval Γ a * (quotientPrefix Γ a - quotientPrefix Γ b) = 1 := by
    rw [mul_sub, quotientRemoval_mul_quotientPrefix,
      quotientRemoval_mul_quotientPrefix]
    simp [hab]
  rw [dist_eq_norm]
  calc
    1 ≤ ‖(1 : ShiftQuotient Γ)‖ := one_le_norm_one _
    _ = ‖quotientRemoval Γ a * (quotientPrefix Γ a - quotientPrefix Γ b)‖ :=
      congrArg norm hrelation.symm
    _ ≤ ‖quotientRemoval Γ a‖ * ‖quotientPrefix Γ a - quotientPrefix Γ b‖ := norm_mul_le _ _
    _ ≤ 1 * ‖quotientPrefix Γ a - quotientPrefix Γ b‖ :=
      mul_le_mul_of_nonneg_right (norm_quotientRemoval_le Γ a) (norm_nonneg _)
    _ = ‖quotientPrefix Γ a - quotientPrefix Γ b‖ := one_mul _

theorem quotientPrefix_injective : Function.Injective (quotientPrefix Γ) := by
  intro a b h
  by_contra hab
  have hsep := one_le_dist_quotientPrefix Γ hab
  rw [h, dist_self] at hsep
  norm_num at hsep

/-- Every dense subset must approximate all the separated prefix generators. -/
theorem mk_alphabet_le_mk_dense (D : Set (ShiftQuotient Γ)) (hD : Dense D) :
    Cardinal.mk Γ ≤ Cardinal.mk D := by
  classical
  choose p hpD hp using fun a : Γ => hD.exists_dist_lt (quotientPrefix Γ a)
    (show (0 : ℝ) < 1 / 3 by norm_num)
  let f : Γ → D := fun a => ⟨p a, hpD a⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro a b h
  by_contra hab
  have hpab : p a = p b := congrArg Subtype.val h
  have htriangle := dist_triangle (quotientPrefix Γ a) (p a) (quotientPrefix Γ b)
  have hba : dist (p a) (quotientPrefix Γ b) < 1 / 3 := by
    rw [hpab, dist_comm]
    exact hp b
  have hsep := one_le_dist_quotientPrefix Γ hab
  linarith [hp a]

/-- In particular, the actual beth-omega quotient has at least beth-omega elements. -/
theorem bethOmega_le_mk_shiftQuotient :
    bethOmega ≤ Cardinal.mk (ShiftQuotient LargeAlphabet) := by
  rw [← mk_largeAlphabet]
  exact Cardinal.mk_le_of_injective (quotientPrefix_injective LargeAlphabet)

end SurveyStatements.P2
