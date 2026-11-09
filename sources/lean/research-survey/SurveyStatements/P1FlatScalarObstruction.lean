import SurveyStatements.P1RapidAlternative
import SurveyStatements.P1OrderedBlockObstruction

/-! Failure of toroidal separation yields bounded normalized-basis partial
sums whose scalar coefficients do not tend to zero. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem exists_bounded_nonvanishing_flat_coefficients {e : ℕ → X}
    (he : IsAsymptoticallyMonotone e)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n k, n ≠ k → 1 + ε < toroidalDistance (x n) (x k)) :
    ∃ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ 1) ∧ HasBoundedPartialSums e a ∧
      ¬ Tendsto a atTop (𝓝 0) := by
  obtain ⟨m, b, α, hm, hflat, hblocks, hsupp, hα, _, hbound⟩ :=
    rapid_flatBlock_alternative he hno
  have hbnz : ∀ n, b n ≠ 0 := by
    intro n hzero
    have hnonzero := (hblocks n).1
    apply hnonzero
    simp [hzero]
  refine ⟨orderedBlockCoefficients b α,
    orderedFlatBlockCoefficients_norm_le_one m hm b hsupp hflat α hα, ?_,
    orderedFlatBlockCoefficients_not_tendsto_zero m hm b hsupp hflat hbnz α hα⟩
  exact orderedBlockCoefficients_bounded (by norm_num) hp m hm b hsupp α hbound

end SurveyStatements.P1
