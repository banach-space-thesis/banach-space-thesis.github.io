import ThesisCommon.Analysis.Factorization
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! The quantitative final step of the Alspach--Enflo--Odell reduction.
Uniformly bounded retractions compressing each operator arbitrarily close
to a scalar multiple of the identity give a uniform factorisation bound. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

theorem scalar_multiple_factorsIdentityWith {c : 𝕜} (hc : (1 / 2 : ℝ) ≤ ‖c‖) :
    FactorsIdentityWith (c • ContinuousLinearMap.id 𝕜 X) X 2 := by
  have hne : c ≠ 0 := norm_pos_iff.mp (by linarith)
  have hinv : ‖c⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.mpr hne) (by norm_num : (0 : ℝ) < 2)).mpr
      (by simpa using hc)
  refine ⟨c⁻¹ • ContinuousLinearMap.id 𝕜 X, ContinuousLinearMap.id 𝕜 X, ?_, ?_⟩
  · ext x
    simp [smul_smul, hne]
  · have hU : ‖c⁻¹ • ContinuousLinearMap.id 𝕜 X‖ ≤ 2 := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans
        (by simpa using hinv)
    calc
      _ ≤ 2 * 1 := mul_le_mul hU ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num

theorem scalar_multiple_dichotomy (c : 𝕜) :
    FactorsIdentityWith (c • ContinuousLinearMap.id 𝕜 X) X 2 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - c • ContinuousLinearMap.id 𝕜 X) X 2 := by
  by_cases hc : (1 / 2 : ℝ) ≤ ‖c‖
  · exact Or.inl (scalar_multiple_factorsIdentityWith hc)
  · have hsum := norm_add_le c (1 - c)
    have he : c + (1 - c) = (1 : 𝕜) := by ring
    rw [he, norm_one] at hsum
    have hcomp : ContinuousLinearMap.id 𝕜 X - c • ContinuousLinearMap.id 𝕜 X =
        (1 - c) • ContinuousLinearMap.id 𝕜 X := by
      ext x
      simp [sub_smul]
    rw [hcomp]
    exact Or.inr (scalar_multiple_factorsIdentityWith (by linarith))

theorem hasCPFP_of_scalar_compressions {C : ℝ}
    (h : ∀ T : X →L[𝕜] X, ∀ ε : ℝ, 0 < ε →
      ∃ A B : X →L[𝕜] X, ∃ c : 𝕜,
        A.comp B = ContinuousLinearMap.id 𝕜 X ∧ ‖A‖ * ‖B‖ ≤ C ∧
        ‖(A.comp T).comp B - c • ContinuousLinearMap.id 𝕜 X‖ < ε) :
    HasCPFP 𝕜 X (4 * C) := by
  intro T
  obtain ⟨A, B, c, hAB, hnorm, hsmall⟩ := h T (1 / 8) (by norm_num)
  have hpert := factorization_dichotomy_perturb (scalar_multiple_dichotomy (X := X) c)
    (by linarith : 2 * ‖(A.comp T).comp B - c • ContinuousLinearMap.id 𝕜 X‖ < 1 / 2)
  rcases hpert with hT | hT
  · exact Or.inl ((hT.of_compression A B).mono (by nlinarith))
  · rw [← compression_complement T A B hAB] at hT
    exact Or.inr ((hT.of_compression A B).mono (by nlinarith))

theorem hasUPFP_of_scalar_compressions {C : ℝ}
    (h : ∀ T : X →L[𝕜] X, ∀ ε : ℝ, 0 < ε →
      ∃ A B : X →L[𝕜] X, ∃ c : 𝕜,
        A.comp B = ContinuousLinearMap.id 𝕜 X ∧ ‖A‖ * ‖B‖ ≤ C ∧
        ‖(A.comp T).comp B - c • ContinuousLinearMap.id 𝕜 X‖ < ε) : HasUPFP 𝕜 X := by
  refine ⟨max 1 (4 * C), le_max_left _ _, fun T => ?_⟩
  exact (hasCPFP_of_scalar_compressions h T).imp
    (fun hT => hT.mono (le_max_right _ _)) (fun hT => hT.mono (le_max_right _ _))

end ThesisCommon
