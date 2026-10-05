import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace ThesisCommon
variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]

theorem opNorm_eq_zero_iff_of_seminormed_domain (T : A →L[𝕜] B) :
    ‖T‖ = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    apply norm_le_zero_iff.mp
    calc
      ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ = 0 := by rw [h, zero_mul]
  · intro h
    simp [h]

end ThesisCommon
