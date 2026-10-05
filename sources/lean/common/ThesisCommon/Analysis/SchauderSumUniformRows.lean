import ThesisCommon.Analysis.SchauderSumInsertion

/-! Outer weak nullity controls every unit-ball vector in a sufficiently
late fibre. No basis or weak-null assumption is needed on the inner space. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem uniform_unit_ball_row_bound
    (hwb : ∀ ψ : X →L[𝕜] 𝕜, Tendsto (fun i => ψ (b.vector i)) atTop (𝓝 0))
    (φ : SchauderSum b hb Y →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ i, N ≤ i → ∀ y : Y, ‖y‖ ≤ 1 → ‖φ (single i y)‖ < ε := by
  classical
  have hw (i : ℕ) : ∃ y : Y, ‖y‖ ≤ 1 ∧
      ((∃ z : Y, ‖z‖ ≤ 1 ∧ ε ≤ ‖φ (single i z)‖) → ε ≤ ‖φ (single i y)‖) := by
    by_cases hi : ∃ z : Y, ‖z‖ ≤ 1 ∧ ε ≤ ‖φ (single i z)‖
    · obtain ⟨y, hy, hφ⟩ := hi
      exact ⟨y, hy, fun _ => hφ⟩
    · exact ⟨0, by simp, fun h => (hi h).elim⟩
  choose y hy hbad using hw
  obtain ⟨B, _, hB⟩ := exists_vector_insertion (b := b) (hb := hb) y hy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hwb (φ.comp B)) ε hε
  refine ⟨N, ?_⟩
  intro i hi z hz
  have hsmall : ‖φ (single i (y i))‖ < ε := by
    simpa only [dist_zero_right, ContinuousLinearMap.comp_apply, hB] using hN i hi
  by_contra h
  exact (not_le_of_gt hsmall) (hbad i ⟨z, hz, le_of_not_gt h⟩)

end SchauderSum
end ThesisCommon
