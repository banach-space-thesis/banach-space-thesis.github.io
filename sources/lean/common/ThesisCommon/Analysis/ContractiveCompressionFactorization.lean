import ThesisCommon.Analysis.SharpFactorization

/-! The exact bound six in the James-tree factorization assembly. A proved
left inverse of norm at most three is corrected after a contractive
compression differs from its model by at most one sixth. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem factorsIdentityWith_six_of_near_compression_left_inverse
    (Q : Y →L[𝕜] Y) (A : Y →L[𝕜] X) (B : X →L[𝕜] Y)
    (D R : X →L[𝕜] X) (hRD : R.comp D = ContinuousLinearMap.id 𝕜 X)
    (hR : ‖R‖ ≤ 3) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (herr : ‖(A.comp Q).comp B - D‖ ≤ 1/6) : FactorsIdentityWith Q X 6 := by
  have hD : FactorsIdentityWith D X 3 := by
    refine ⟨R, ContinuousLinearMap.id 𝕜 X, ?_, ?_⟩
    · simpa only [ContinuousLinearMap.comp_id] using hRD
    · calc
        ‖R‖ * ‖ContinuousLinearMap.id 𝕜 X‖ ≤ ‖R‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg R)
        _ ≤ 3 := by simpa only [mul_one] using hR
  have hsmall : 3 * ‖(A.comp Q).comp B - D‖ ≤ (1/2 : ℝ) := by linarith
  have hcorrected : FactorsIdentityWith ((A.comp Q).comp B) X 6 := by
    simpa only [show (3 : ℝ) / (1 - (1/2)) = 6 by norm_num] using
      hD.perturb_fraction (by norm_num : (1/2 : ℝ) < 1) hsmall
  apply (hcorrected.of_compression A B).mono
  have hnorm : ‖A‖ * ‖B‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hA hB (norm_nonneg B) zero_le_one
  linarith

end ThesisCommon
