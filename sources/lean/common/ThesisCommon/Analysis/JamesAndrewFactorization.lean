import ThesisCommon.Analysis.JamesAndrewCompression

/-! The small sampling compression gives actual identity factors. The
reading factor is an automorphism followed by coordinate sampling, so its
kernel remains the concrete sampling kernel needed for primarity. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

theorem exists_correction_equiv_of_norm_sub_id_lt_half (B : X →L[𝕜] X)
    (hB : ‖B - ContinuousLinearMap.id 𝕜 X‖ < 1 / 2) :
    ∃ E : X ≃L[𝕜] X, E.toContinuousLinearMap.comp B = ContinuousLinearMap.id 𝕜 X ∧
      ‖E.toContinuousLinearMap‖ ≤ 2 := by
  let F : X →L[𝕜] X := ContinuousLinearMap.id 𝕜 X - B
  have hF : ‖F‖ < 1 / 2 := by simpa only [F, norm_sub_rev] using hB
  have hF1 : ‖F‖ < 1 := by linarith
  let W : (X →L[𝕜] X)ˣ := Units.oneSub F hF1
  have hW : (W : X →L[𝕜] X) = B := by
    change ContinuousLinearMap.id 𝕜 X - (ContinuousLinearMap.id 𝕜 X - B) = B
    abel
  refine ⟨ContinuousLinearEquiv.ofUnit W⁻¹, ?_, ?_⟩
  · change (↑W⁻¹ : X →L[𝕜] X).comp B = _
    rw [← hW]
    exact W.inv_val
  · have hg := tsum_geometric_le_of_norm_lt_one F hF1
    have hid : ‖(1 : X →L[𝕜] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hpos : 0 < 1 - ‖F‖ := by linarith
    have hi : (1 - ‖F‖)⁻¹ ≤ (2 : ℝ) := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      linarith
    change ‖∑' n : ℕ, F ^ n‖ ≤ 2
    linarith

variable (p : BanachExponent) (hp : p.val ≠ ⊤) (hpl : 1 < p.val.toReal)

theorem james_scalar_one_factors_with_sampling
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (hscalar : jamesOperatorScalar p hp hpl T = 1) :
    ∃ (α β : ℕ → ℕ) (hα : StrictMono α) (hβ : StrictMono β)
      (E : JamesSequenceSpace 𝕜 p ≃L[𝕜] JamesSequenceSpace 𝕜 p),
      ((E.toContinuousLinearMap.comp (jamesSample (𝕜 := 𝕜) p hp α hα)).comp T).comp
          (jamesPrefixRepeat (𝕜 := 𝕜) p hp β hβ) = ContinuousLinearMap.id 𝕜 _ ∧
      ‖E.toContinuousLinearMap‖ ≤ 2 := by
  obtain ⟨α, β, hα, hβ, hsmall⟩ := exists_james_small_prefix_compression p hp hpl T hscalar
  obtain ⟨E, hE, hnorm⟩ := exists_correction_equiv_of_norm_sub_id_lt_half _ hsmall
  refine ⟨α, β, hα, hβ, E, ?_, hnorm⟩
  simpa only [ContinuousLinearMap.comp_assoc] using hE

theorem james_scalar_one_factors_identity
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (hscalar : jamesOperatorScalar p hp hpl T = 1) :
    FactorsIdentityWith T (JamesSequenceSpace 𝕜 p) 2 := by
  obtain ⟨α, β, hα, hβ, E, hE, hnorm⟩ := james_scalar_one_factors_with_sampling p hp hpl T hscalar
  refine ⟨E.toContinuousLinearMap.comp (jamesSample (𝕜 := 𝕜) p hp α hα),
    jamesPrefixRepeat (𝕜 := 𝕜) p hp β hβ, hE, ?_⟩
  have hread : ‖E.toContinuousLinearMap.comp (jamesSample (𝕜 := 𝕜) p hp α hα)‖ ≤ 2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hnorm (jamesSample_norm_le p hp α hα) (norm_nonneg _) (by norm_num)).trans_eq
        (mul_one _))
  exact (mul_le_mul hread (jamesPrefixRepeat_norm_le p hp β hβ)
    (norm_nonneg _) (by norm_num)).trans_eq (mul_one _)

theorem james_nonzero_scalar_factors_identity
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (hscalar : jamesOperatorScalar p hp hpl T ≠ 0) :
    FactorsIdentityWith T (JamesSequenceSpace 𝕜 p)
      (2 * ‖jamesOperatorScalar p hp hpl T‖⁻¹) := by
  let c := jamesOperatorScalar p hp hpl T
  have hc : jamesOperatorScalar p hp hpl (c⁻¹ • T) = 1 := by
    rw [jamesOperatorScalar_smul]
    exact inv_mul_cancel₀ hscalar
  obtain ⟨U, V, heq, hnorm⟩ := james_scalar_one_factors_identity p hp hpl (c⁻¹ • T) hc
  refine ⟨c⁻¹ • U, V, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using heq
  · rw [norm_smul, norm_inv]
    calc
      (‖c‖⁻¹ * ‖U‖) * ‖V‖ = ‖c‖⁻¹ * (‖U‖ * ‖V‖) := by ring
      _ ≤ ‖c‖⁻¹ * 2 := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by ring

include hp hpl in
theorem james_nonweaklyCompact_factors_identity
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (hT : ¬ IsWeaklyCompactOperator T) : FactorsIdentity T (JamesSequenceSpace 𝕜 p) :=
  (james_nonzero_scalar_factors_identity p hp hpl T
    (fun h => hT ((james_weaklyCompact_iff_scalar_eq_zero p hp hpl T).mpr h))).forget_bound

end ThesisCommon
