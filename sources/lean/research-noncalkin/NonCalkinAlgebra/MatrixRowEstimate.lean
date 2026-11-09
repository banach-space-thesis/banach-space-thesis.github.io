import NonCalkinAlgebra.MatrixUnits

noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]

theorem coefficientSpace_norm_eq_tsum (x : CoefficientSpace D) :
    ‖x‖ = ∑' j : ℕ, ‖x j‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by norm_num) x

theorem coefficientSpace_summable_norm (x : CoefficientSpace D) :
    Summable (fun j : ℕ => ‖x j‖) := by
  simpa using (lp.memℓp x).summable (show (0 : ℝ) < (1 : ENNReal).toReal by norm_num)

theorem coefficientSpace_sum_norm_le (x : CoefficientSpace D) (F : Finset ℕ) :
    ∑ j ∈ F, ‖x j‖ ≤ ‖x‖ := by
  rw [coefficientSpace_norm_eq_tsum]
  exact (coefficientSpace_summable_norm D x).sum_le_tsum F (fun j _ => norm_nonneg (x j))

theorem finite_row_vector_bound (F : Finset ℕ) (a : F → ℂ) (x : CoefficientSpace D) :
    ‖∑ j : F, a j • x j.val‖ ≤ ‖a‖ * ‖x‖ := by
  calc
    ‖∑ j : F, a j • x j.val‖ ≤ ∑ j : F, ‖a j • x j.val‖ := norm_sum_le _ _
    _ = ∑ j : F, ‖a j‖ * ‖x j.val‖ := by simp only [norm_smul]
    _ ≤ ∑ j : F, ‖a‖ * ‖x j.val‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm a j) (norm_nonneg _)
    _ = ‖a‖ * ∑ j : F, ‖x j.val‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖a‖ * ‖x‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
      exact (Finset.sum_coe_sort F (fun j : ℕ => ‖x j‖)).le.trans
        (coefficientSpace_sum_norm_le D x F)

theorem scalarMatrixUnit_row_apply (i : ℕ) (F : Finset ℕ) (a : F → ℂ)
    (x : CoefficientSpace D) :
    (∑ j : F, a j • scalarMatrixUnit D i j.val) x =
      lp.single 1 i (∑ j : F, a j • x j.val) := by
  classical
  ext n
  by_cases hn : n = i
  · subst n
    simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      scalarMatrixUnit, theta_apply, lp.single_apply]
  · simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      scalarMatrixUnit, theta_apply, lp.single_apply, hn]

/-- The first-row estimate in Lemma 5.2, including the trivial empty-set case. -/
theorem norm_scalarMatrixUnit_row_le (i : ℕ) (F : Finset ℕ) (a : F → ℂ) :
    ‖∑ j : F, a j • scalarMatrixUnit D i j.val‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro x
  rw [scalarMatrixUnit_row_apply, lp.norm_single zero_lt_one]
  exact finite_row_vector_bound D F a x

end NonCalkinAlgebra
