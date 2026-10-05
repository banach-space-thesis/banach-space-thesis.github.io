import ThesisCommon.Analysis.ComplexL1OperatorModulus
import ThesisCommon.Analysis.L1OperatorModulus

/-! Real coordinates produce a genuine four-positive-operator decomposition
of every complex L1 operator. All real L1 operators complexify isometrically. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem complexL1Operator_ext_ofReal (T U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (h : ∀ f : Lp ℝ 1 μ, T (complexL1OfReal μ f) = U (complexL1OfReal μ f)) : T = U := by
  ext1 f
  calc
    T f = T (complexL1OfReal μ (complexL1Re μ f)) +
        Complex.I • T (complexL1OfReal μ (complexL1Im μ f)) := by
      rw [← map_smul, ← map_add, complexL1_decomposition]
    _ = U (complexL1OfReal μ (complexL1Re μ f)) +
        Complex.I • U (complexL1OfReal μ (complexL1Im μ f)) := by rw [h,h]
    _ = U f := by rw [← map_smul, ← map_add, complexL1_decomposition]

theorem complexL1Extension_sub (S R : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    complexL1Extension (S-R) = complexL1Extension S - complexL1Extension R := by
  apply complexL1Operator_ext_ofReal
  intro f
  simp [complexL1Extension_ofReal]

theorem complexL1Operator_decomposition (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    T = complexL1Extension ((complexL1Re ν).comp (complexL1OperatorRealRestriction T)) +
      Complex.I • complexL1Extension ((complexL1Im ν).comp (complexL1OperatorRealRestriction T)) := by
  apply complexL1Operator_ext_ofReal
  intro f
  simpa [complexL1Extension_ofReal, complexL1OperatorRealRestriction] using
    (complexL1_decomposition (T (complexL1OfReal μ f))).symm

theorem complexL1_operator_regular (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ∃ P Q R S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν,
      (∀ f, 0 ≤ f → 0 ≤ P f) ∧ (∀ f, 0 ≤ f → 0 ≤ Q f) ∧
      (∀ f, 0 ≤ f → 0 ≤ R f) ∧ (∀ f, 0 ≤ f → 0 ≤ S f) ∧
      T = complexL1Extension P - complexL1Extension Q +
        Complex.I • (complexL1Extension R - complexL1Extension S) := by
  obtain ⟨P,Q,hP,hQ,hPQ⟩ := lOne_operator_regular
    ((complexL1Re ν).comp (complexL1OperatorRealRestriction T))
  obtain ⟨R,S,hR,hS,hRS⟩ := lOne_operator_regular
    ((complexL1Im ν).comp (complexL1OperatorRealRestriction T))
  refine ⟨P,Q,R,S,hP,hQ,hR,hS,?_⟩
  rw [complexL1Operator_decomposition T, hPQ, hRS, complexL1Extension_sub, complexL1Extension_sub]

theorem complexL1Extension_modulus_le_realModulus (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (f : Lp ℂ 1 μ) :
    complexL1Modulus (complexL1Extension S f) ≤ lOneOperatorModulus S (complexL1Modulus f) := by
  apply complexL1_domination_of_nonneg (complexL1Extension S) (lOneOperatorModulus S) ?_ f
  intro g hg
  rw [complexL1Extension_ofReal, complexL1Modulus_ofReal]
  simpa only [abs_of_nonneg hg] using lOneOperatorModulus_dominates S g

/-- Complexifying a real L1 operator preserves its norm, even without positivity. -/
theorem norm_complexL1Extension (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ‖complexL1Extension S‖ = ‖S‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S)
    intro f
    calc
      ‖complexL1Extension S f‖ = ‖complexL1Modulus (complexL1Extension S f)‖ :=
        (norm_complexL1Modulus _).symm
      _ ≤ ‖lOneOperatorModulus S (complexL1Modulus f)‖ := norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg (complexL1Modulus_nonneg _),
          abs_of_nonneg (lOneOperatorModulus_nonneg S _ (complexL1Modulus_nonneg _))]
        exact complexL1Extension_modulus_le_realModulus S f)
      _ ≤ ‖lOneOperatorModulus S‖ * ‖complexL1Modulus f‖ := (lOneOperatorModulus S).le_opNorm _
      _ = ‖S‖ * ‖f‖ := by rw [norm_complexL1Modulus,norm_lOneOperatorModulus]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    calc
      ‖S f‖ = ‖complexL1OfReal ν (S f)‖ := (norm_complexL1OfReal _).symm
      _ = ‖complexL1Extension S (complexL1OfReal μ f)‖ := by rw [complexL1Extension_ofReal]
      _ ≤ ‖complexL1Extension S‖ * ‖complexL1OfReal μ f‖ := (complexL1Extension S).le_opNorm _
      _ = ‖complexL1Extension S‖ * ‖f‖ := by rw [norm_complexL1OfReal]

end ThesisCommon
