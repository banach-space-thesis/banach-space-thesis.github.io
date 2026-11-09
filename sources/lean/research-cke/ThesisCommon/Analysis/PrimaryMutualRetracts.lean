import ThesisCommon.Analysis.Factorization

/-! Quantitative UPFP transfer between mutually complemented embeddings.
This allows the mean-zero Haar space to supply the full interval Lp result.
Both retraction identities are hypotheses about actual bounded maps. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem FactorsIdentityWith.retract_factor_space {T : Z →L[𝕜] Z} {C : ℝ}
    (h : FactorsIdentityWith T Y C) (A : Y →L[𝕜] X) (B : X →L[𝕜] Y)
    (hAB : A.comp B = ContinuousLinearMap.id 𝕜 X) :
    FactorsIdentityWith T X (C * (‖A‖ * ‖B‖)) := by
  obtain ⟨U, V, heq, hn⟩ := h
  refine ⟨A.comp U, V.comp B, ?_, ?_⟩
  · calc
      ((A.comp U).comp T).comp (V.comp B) =
          A.comp (((U.comp T).comp V).comp B) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = ContinuousLinearMap.id 𝕜 X := by rw [heq]; simpa using hAB
  · calc
      ‖A.comp U‖ * ‖V.comp B‖ ≤ (‖A‖ * ‖U‖) * (‖V‖ * ‖B‖) :=
        mul_le_mul (A.opNorm_comp_le U) (V.opNorm_comp_le B)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖U‖ * ‖V‖) * (‖A‖ * ‖B‖) := by ring
      _ ≤ C * (‖A‖ * ‖B‖) :=
        mul_le_mul_of_nonneg_right hn (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem HasCPFP.of_mutual_retracts {C : ℝ} (h : HasCPFP 𝕜 Y C)
    (P : X →L[𝕜] Y) (J : Y →L[𝕜] X)
    (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 Y)
    (A : Y →L[𝕜] X) (B : X →L[𝕜] Y)
    (hAB : A.comp B = ContinuousLinearMap.id 𝕜 X) :
    HasCPFP 𝕜 X ((C * (‖P‖ * ‖J‖)) * (‖A‖ * ‖B‖)) := by
  intro T
  rcases h ((P.comp T).comp J) with hT | hT
  · exact Or.inl ((hT.of_compression P J).retract_factor_space A B hAB)
  · rw [← compression_complement T P J hPJ] at hT
    exact Or.inr ((hT.of_compression P J).retract_factor_space A B hAB)

theorem HasUPFP.of_mutual_retracts (h : HasUPFP 𝕜 Y)
    (P : X →L[𝕜] Y) (J : Y →L[𝕜] X)
    (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 Y)
    (A : Y →L[𝕜] X) (B : X →L[𝕜] Y)
    (hAB : A.comp B = ContinuousLinearMap.id 𝕜 X) : HasUPFP 𝕜 X := by
  obtain ⟨C, _, hC⟩ := h
  let D := (C * (‖P‖ * ‖J‖)) * (‖A‖ * ‖B‖)
  refine ⟨max 1 D, le_max_left _ _, fun T => ?_⟩
  exact (hC.of_mutual_retracts P J hPJ A B hAB T).imp
    (fun hT => hT.mono (le_max_right _ _))
    (fun hT => hT.mono (le_max_right _ _))

end ThesisCommon
