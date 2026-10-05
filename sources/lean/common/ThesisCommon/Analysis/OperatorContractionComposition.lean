import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Norm control for a composition of two genuine contractions. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem norm_comp_of_contractions_le_one (A : F →L[𝕜] G) (B : E →L[𝕜] F)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A.comp B‖ ≤ 1 :=
  (A.opNorm_comp_le B).trans ((mul_le_mul hA hB (norm_nonneg B) zero_le_one).trans_eq (mul_one 1))

end ThesisCommon

