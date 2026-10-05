import JFA.CountableDual
import JFA.RightSlice
import Mathlib.Tactic.Ring

/-! The countable norming dual family also determines the injective tensor norm.
This is the norm control needed for a separable function-space representation. -/

noncomputable section
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {F X : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem norm_le_of_norming_slices_le (z : InjectiveTensor 𝕜 F X) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, ‖leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n) z‖ ≤ c) : ‖z‖ ≤ c := by
  change ‖z.val‖ ≤ c
  apply (dualOperator_norm_le_iff z.val c hc).mpr
  intro φ ψ
  have hright : ‖rightSlice ψ z‖ ≤ ‖ψ‖ * c := by
    apply norm_le_of_normingSequence_le (𝕜 := 𝕜)
    intro n
    rw [rightSlice_pairing]
    exact (ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h n) (norm_nonneg ψ))
  calc
    ‖ψ (z.val φ)‖ = ‖φ (rightSlice ψ z)‖ := congrArg norm (rightSlice_pairing ψ φ z).symm
    _ ≤ ‖φ‖ * ‖rightSlice ψ z‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (‖ψ‖ * c) := mul_le_mul_of_nonneg_left hright (norm_nonneg φ)
    _ = (c * ‖φ‖) * ‖ψ‖ := by ring

theorem eq_zero_of_norming_slices_zero (z : InjectiveTensor 𝕜 F X)
    (h : ∀ n, leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n) z = 0) : z = 0 := by
  apply norm_le_zero_iff.mp
  apply norm_le_of_norming_slices_le z le_rfl
  intro n
  rw [h n, norm_zero]

end JFA
