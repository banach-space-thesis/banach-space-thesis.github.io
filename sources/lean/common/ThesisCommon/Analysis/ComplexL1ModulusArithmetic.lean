import ThesisCommon.Analysis.ComplexL1OperatorPhases

/-! Basic arithmetic of the genuinely constructed complex operator modulus. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

@[simp] theorem complexL1OperatorRe_sub (T U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorRe (T-U) = complexL1OperatorRe T - complexL1OperatorRe U := by
  ext1 f
  simp [complexL1OperatorRe,complexL1OperatorRealRestriction]

@[simp] theorem complexL1OperatorIm_sub (T U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorIm (T-U) = complexL1OperatorIm T - complexL1OperatorIm U := by
  ext1 f
  simp [complexL1OperatorIm,complexL1OperatorRealRestriction]

theorem complexL1OperatorPhase_sub (T U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (c : ℂ) :
    complexL1OperatorPhase (T-U) c = complexL1OperatorPhase T c - complexL1OperatorPhase U c := by
  simp only [complexL1OperatorPhase,complexL1OperatorRe_sub,complexL1OperatorIm_sub,smul_sub]
  abel

theorem complexL1OperatorModulus_zero :
    complexL1OperatorModulus (0 : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) = 0 := by
  apply norm_eq_zero.mp
  rw [norm_complexL1OperatorModulus,norm_zero]

theorem complexL1OperatorModulus_add_le (T U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus (T+U) ≤ complexL1OperatorModulus T + complexL1OperatorModulus U := by
  apply complexL1OperatorModulus_least
  intro f hf
  change complexL1Modulus (T (complexL1OfReal μ f) + U (complexL1OfReal μ f)) ≤ _
  exact (complexL1Modulus_add_le _ _).trans
    (add_le_add (complexOperatorModulus_dominates_nonneg (complexL1OperatorRealRestriction T) f hf)
      (complexOperatorModulus_dominates_nonneg (complexL1OperatorRealRestriction U) f hf))

end ThesisCommon
