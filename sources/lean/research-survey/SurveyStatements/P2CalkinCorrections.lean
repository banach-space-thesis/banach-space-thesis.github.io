import SurveyStatements.P2Calkin
import Mathlib.Tactic.Linarith

/-! The quotient norm supplies genuine compact corrections to row representatives. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_compactCorrection_norm_le (T : BoundedOperators X) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hquot : ‖calkinQuotient X T‖ ≤ D * C) :
    ∃ K : BoundedOperators X, IsCompactOperator K ∧ ‖T + K‖ ≤ (D + 1) * C := by
  by_cases hzero : C = 0
  · have hT : IsCompactOperator T := by
      apply (calkinQuotient_eq_zero_iff X T).mp
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [hzero, mul_zero] using hquot
    exact ⟨-T, hT.neg, by simp [hzero]⟩
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
    obtain ⟨V, hV, hnV⟩ := Submodule.Quotient.norm_mk_lt (calkinQuotient X T) hCpos
    refine ⟨V - T, ?_, ?_⟩
    · apply (calkinQuotient_eq_zero_iff X (V - T)).mp
      change (CompactOperators X).mkQ (V - T) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hV
    · have heq : T + (V - T) = V := by abel
      rw [heq]
      nlinarith

end SurveyStatements.P2
