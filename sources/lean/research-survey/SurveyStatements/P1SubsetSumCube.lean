import SurveyStatements.P1ComplexCoefficients
import SurveyStatements.P1BasicSelection

/-! Arbitrary complex finite coefficients from a uniform subset-sum bound.
Real and imaginary sign selection supplies the factor four, with the actual
complex Hahn--Banach functional providing the norm estimate. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem finite_complex_subsetSum_cube_bound {ι : Type*}
    (F : Finset ι) (u : ι → X) {B R : ℝ} (hR : 0 ≤ R)
    (hB : ∀ S : Finset ι, S ⊆ F → ‖∑ i ∈ S, u i‖ ≤ B)
    (a : ι → ℂ) (ha : ∀ i ∈ F, ‖a i‖ ≤ R) :
    ‖∑ i ∈ F, a i • u i‖ ≤ (4 * B) * R := by
  classical
  have hBnonneg : 0 ≤ B := by simpa using hB ∅ (Finset.empty_subset F)
  let x := ∑ i ∈ F, a i • u i
  by_cases hx : x = 0
  · change ‖x‖ ≤ _
    rw [hx, norm_zero]
    positivity
  obtain ⟨f, hfnorm, hfx⟩ := exists_dual_vector ℂ x hx
  obtain ⟨S, hSF, hmass⟩ := exists_complex_coefficient_subset F (fun i => f (u i))
  have hsub : ‖∑ i ∈ S, f (u i)‖ ≤ B := by
    rw [← map_sum]
    exact (f.le_opNorm _).trans (by simpa only [hfnorm, one_mul] using hB S hSF)
  have hsum : ∑ i ∈ F, ‖f (u i)‖ ≤ 4 * B := by linarith
  have hnormx : ‖x‖ = ‖f x‖ := by rw [hfx]; simp
  calc
    _ = ‖f x‖ := hnormx
    _ = ‖∑ i ∈ F, a i • f (u i)‖ := by simp only [x, map_sum, map_smul]
    _ ≤ ∑ i ∈ F, ‖a i • f (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ F, R * ‖f (u i)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (ha i hi) (norm_nonneg _)
    _ = R * (∑ i ∈ F, ‖f (u i)‖) := by rw [Finset.mul_sum]
    _ ≤ R * (4 * B) := mul_le_mul_of_nonneg_left hsum hR
    _ = (4 * B) * R := mul_comm _ _

end SurveyStatements.P1
