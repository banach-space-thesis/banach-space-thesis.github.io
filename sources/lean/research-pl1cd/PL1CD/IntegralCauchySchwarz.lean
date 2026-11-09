import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory

namespace PL1CD.Entropy

theorem integral_mul_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u v : Ω → ℝ) (hu : Integrable (fun x => u x ^ 2) μ)
    (hv : Integrable (fun x => v x ^ 2) μ) (huv : Integrable (fun x => u x * v x) μ) :
    (∫ x, u x * v x ∂μ) ^ 2 ≤ (∫ x, u x ^ 2 ∂μ) * ∫ x, v x ^ 2 ∂μ := by
  have hpoly (t : ℝ) : 0 ≤ (∫ x, u x ^ 2 ∂μ) * (t * t) +
      (-2 * ∫ x, u x * v x ∂μ) * t + ∫ x, v x ^ 2 ∂μ := by
    have hnonneg : 0 ≤ ∫ x, (t * u x - v x) ^ 2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg _)
    have heq : (fun x => (t * u x - v x) ^ 2) =
        (fun x => (t ^ 2) * u x ^ 2 - (2 * t) * (u x * v x) + v x ^ 2) := by
      funext x
      ring
    have hfirst : (∫ x, (t * u x - v x) ^ 2 ∂μ) =
        (∫ x, t ^ 2 * u x ^ 2 - (2 * t) * (u x * v x) ∂μ) + ∫ x, v x ^ 2 ∂μ := by
      rw [heq]
      exact integral_add ((hu.const_mul (t ^ (2 : ℕ))).sub (huv.const_mul (2 * t))) hv
    have hsecond : (∫ x, t ^ 2 * u x ^ 2 - (2 * t) * (u x * v x) ∂μ) =
        (t ^ 2) * (∫ x, u x ^ 2 ∂μ) - (2 * t) * ∫ x, u x * v x ∂μ := by
      calc
        _ = (∫ x, t ^ 2 * u x ^ 2 ∂μ) - ∫ x, (2 * t) * (u x * v x) ∂μ :=
          integral_sub (hu.const_mul (t ^ (2 : ℕ))) (huv.const_mul (2 * t))
        _ = _ := by rw [integral_const_mul, integral_const_mul]
    rw [hfirst, hsecond] at hnonneg
    nlinarith
  have h := discrim_le_zero hpoly
  dsimp [discrim] at h
  nlinarith

end PL1CD.Entropy
