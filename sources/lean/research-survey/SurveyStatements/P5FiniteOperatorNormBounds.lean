import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Ring

/-! Finite composition estimates stated before instantiating the concrete
Bochner spaces. This keeps the norm argument independent of their definitions. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P5

theorem norm_finite_compositions_le {𝕜 X ι : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (s : Finset ι) (A B : ι → X →L[𝕜] X) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hA : ∀ i ∈ s, ‖A i‖ ≤ b i)
    (hB : ∀ i ∈ s, ‖B i‖ ≤ 4) :
    ‖∑ i ∈ s, (A i).comp (B i)‖ ≤ 4 * ∑ i ∈ s, b i := by
  calc
    _ ≤ ∑ i ∈ s, ‖(A i).comp (B i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, b i * 4 := by
      apply Finset.sum_le_sum
      intro i hi
      exact ((A i).opNorm_comp_le (B i)).trans
        (mul_le_mul (hA i hi) (hB i hi) (norm_nonneg (B i)) (hb i hi))
    _ = _ := by rw [← Finset.sum_mul]; ring

end SurveyStatements.P5
