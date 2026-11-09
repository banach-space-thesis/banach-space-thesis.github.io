import SurveyStatements.P5ScalarCompression

/-! Quantitative factorization transfer through bounded complemented copies. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P5

variable {𝕜 X Y : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

theorem uniformPrimaryFactorization_of_bounded_cancellative_compression
    (h : HasScalarCompression 𝕜 Y)
    (P : X →L[𝕜] Y) (ι : Y →L[𝕜] X)
    (hPι : P.comp ι = ContinuousLinearMap.id 𝕜 Y)
    (U : X →L[𝕜] Y) (V : Y →L[𝕜] X)
    (hVU : V.comp U = ContinuousLinearMap.id 𝕜 X)
    (hP : ‖P‖ ≤ 4) (hι : ‖ι‖ ≤ 1) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 4) :
    HasUniformPrimaryFactorization 𝕜 X := by
  have hPιn : ‖P‖ * ‖ι‖ ≤ 4 :=
    (mul_le_mul hP hι (norm_nonneg ι) (by norm_num)).trans (by norm_num)
  have hVUn : ‖V‖ * ‖U‖ ≤ 4 :=
    (mul_le_mul hV hU (norm_nonneg U) (by norm_num)).trans (by norm_num)
  have lift (T : X →L[𝕜] X) (hT : FactorsIdentityWith ((P.comp T).comp ι) Y 3) :
      FactorsIdentityWith T X 48 := by
    apply ((hT.of_compression P ι).through_retract U V hVU).mono
    calc
      (3 * (‖P‖ * ‖ι‖)) * (‖V‖ * ‖U‖) ≤ (3 * 4) * 4 := by gcongr
      _ = 48 := by norm_num
  refine ⟨48, by norm_num, fun T => ?_⟩
  rcases scalarCompression_factor_dichotomy h ((P.comp T).comp ι) with hT | hT
  · obtain ⟨A, B, heq, hnorm⟩ := lift T hT
    exact ⟨A, B, hnorm, Or.inl heq⟩
  · have hc : FactorsIdentityWith
        ((P.comp (ContinuousLinearMap.id 𝕜 X - T)).comp ι) Y 3 := by
      rwa [compression_complement T P ι hPι]
    obtain ⟨A, B, heq, hnorm⟩ := lift _ hc
    exact ⟨A, B, hnorm, Or.inr heq⟩

end SurveyStatements.P5
