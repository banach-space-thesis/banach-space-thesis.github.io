import ThesisCommon.Analysis.QuantitativeNeumannInverse

/-! A quantitative scalar-neighbourhood inverse, and its complementary
operator dichotomy. The inverse bound is the endpoint four. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

theorem exists_inverse_of_near_scalar_half (S : E →L[𝕜] E) (c : 𝕜)
    (hc : (1 : ℝ) / 2 ≤ ‖c‖)
    (hclose : ‖S - c • ContinuousLinearMap.id 𝕜 E‖ ≤ 1 / 4) :
    ∃ R : E →L[𝕜] E, R.comp S = ContinuousLinearMap.id 𝕜 E ∧
      S.comp R = ContinuousLinearMap.id 𝕜 E ∧ ‖R‖ ≤ 4 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    exact ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _, by simp⟩
  letI := hE
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (by norm_num) hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hcinv : ‖c⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    simpa only [one_div] using (one_div_le hcpos (by norm_num : (0 : ℝ) < 2)).mpr hc
  let F : E →L[𝕜] E := c⁻¹ • S
  have hid : ContinuousLinearMap.id 𝕜 E - F =
      c⁻¹ • (c • ContinuousLinearMap.id 𝕜 E - S) := by
    simp only [F, smul_sub, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hF : ‖ContinuousLinearMap.id 𝕜 E - F‖ ≤ 1 / 2 := by
    rw [hid, norm_smul, norm_sub_rev]
    calc
      _ ≤ ‖c⁻¹‖ * (1 / 4) := mul_le_mul_of_nonneg_left hclose (norm_nonneg _)
      _ ≤ 2 * (1 / 4) := mul_le_mul_of_nonneg_right hcinv (by norm_num)
      _ = _ := by norm_num
  obtain ⟨G, hGF, hFG, hG⟩ := exists_bounded_inverse_near_identity F
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) hF
  have hG' : ‖G‖ ≤ 2 := by norm_num at hG ⊢; exact hG
  refine ⟨c⁻¹ • G, ?_, ?_, ?_⟩
  · simpa only [F, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp] using hGF
  · simpa only [F, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp] using hFG
  · rw [norm_smul]
    calc
      _ ≤ 2 * ‖G‖ := mul_le_mul_of_nonneg_right hcinv (norm_nonneg _)
      _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left hG' (by norm_num)
      _ = _ := by norm_num

theorem exists_inverse_or_complement_of_near_scalar (S : E →L[𝕜] E) (c : 𝕜)
    (hclose : ‖S - c • ContinuousLinearMap.id 𝕜 E‖ ≤ 1 / 4) :
    (∃ R : E →L[𝕜] E, R.comp S = ContinuousLinearMap.id 𝕜 E ∧
      S.comp R = ContinuousLinearMap.id 𝕜 E ∧ ‖R‖ ≤ 4) ∨
    (∃ R : E →L[𝕜] E,
      R.comp (ContinuousLinearMap.id 𝕜 E - S) = ContinuousLinearMap.id 𝕜 E ∧
      (ContinuousLinearMap.id 𝕜 E - S).comp R = ContinuousLinearMap.id 𝕜 E ∧ ‖R‖ ≤ 4) := by
  by_cases hc : (1 : ℝ) / 2 ≤ ‖c‖
  · exact Or.inl (exists_inverse_of_near_scalar_half S c hc hclose)
  have hc' : (1 : ℝ) / 2 ≤ ‖1 - c‖ := by
    have h := norm_add_le c (1 - c)
    have heq : c + (1 - c) = 1 := by ring
    rw [heq, norm_one] at h
    linarith
  apply Or.inr
  apply exists_inverse_of_near_scalar_half (ContinuousLinearMap.id 𝕜 E - S) (1 - c) hc'
  have heq : ContinuousLinearMap.id 𝕜 E - S - (1 - c) • ContinuousLinearMap.id 𝕜 E =
      -(S - c • ContinuousLinearMap.id 𝕜 E) := by
    rw [sub_smul, one_smul]
    abel
  simpa only [heq, norm_neg] using hclose

end ThesisCommon
