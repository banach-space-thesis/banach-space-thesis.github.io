import SurveyStatements.P5OperatorReductionFiniteDisjointification
import SurveyStatements.P5Support.HaarSignSecondMoment

/-! Actual dual-side signed moments on disjoint measurable cells. Small
restrictions and a uniform norm bound imply uniform decay with cell mass. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
open SurveyStatements.P5Support.Grothendieck
variable {𝕜 ι : Type*} [RCLike 𝕜]

theorem restricted_reader_signed_second_moment_le {n : ℕ}
    (s : Fin n → Set ℝ) (hs : ∀ j, MeasurableSet (s j))
    (hd : ∀ j k, j ≠ k → Disjoint (s j) (s k))
    (φ : Fin n → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜)
    (hφ : ∀ j, ‖φ j‖ ≤ 1) (y : Lp 𝕜 1 unitIntervalMeasure)
    {d : ℝ} (hd0 : 0 ≤ d)
    (hsmall : ∀ j, ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s j) (hs j) y‖ ≤ d) :
    mean (fun θ : Fin n → Bool =>
      ‖∑ j, signedValue (θ j) (restrictedFunctional (s j) (hs j) (φ j) y)‖ ^ 2) ≤
        d * ‖y‖ := by
  rw [haar_sign_second_moment]
  apply haar_sign_variance_le
    (fun j => restrictedFunctional (s j) (hs j) (φ j) y) hd0
  · intro j
    change ‖φ j (vectorIndicatorMultiply (𝕜 := 𝕜) (s j) (hs j) y)‖ ≤ d
    have hb : ‖φ j‖ *
        ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s j) (hs j) y‖ ≤ d := by
      calc
        _ ≤ 1 * ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s j) (hs j) y‖ :=
          mul_le_mul_of_nonneg_right (hφ j) (norm_nonneg _)
        _ = ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s j) (hs j) y‖ := one_mul _
        _ ≤ d := hsmall j
    exact ((φ j).le_opNorm _).trans hb
  · simpa using sum_norm_restrictedFunctional_le Finset.univ s hs
      (fun j _ k _ hjk => hd j k hjk) φ (fun j _ => hφ j) y

theorem uniform_restricted_reader_signed_variance_small
    (y : ι → Lp 𝕜 1 unitIntervalMeasure) (hy : UniformSmallRestrictions y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, ‖y i‖ ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, ∀ s : Fin n → Set ℝ, ∀ hs : ∀ j, MeasurableSet (s j),
      (∀ j k, j ≠ k → Disjoint (s j) (s k)) →
      (∀ j, unitIntervalMeasure (s j) ≤ ENNReal.ofReal δ) →
      ∀ φ : Fin n → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜,
      (∀ j, ‖φ j‖ ≤ 1) → ∀ i,
      mean (fun θ : Fin n → Bool =>
        ‖∑ j, signedValue (θ j) (restrictedFunctional (s j) (hs j) (φ j) (y i))‖ ^ 2) < ε := by
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨δ, hδ, hsmall⟩ := hy (ε / (C + 1)) (div_pos hε hC1)
  refine ⟨δ, hδ, fun n s hs hd hμ φ hφ i => ?_⟩
  have hmoment := restricted_reader_signed_second_moment_le s hs hd φ hφ (y i)
    (div_nonneg hε.le hC1.le) (fun j => hsmall i (s j) (hs j) (hμ j))
  have hfrac : ε / (C + 1) * C < ε := by
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ hC1).mpr (by nlinarith)
  exact hmoment.trans_lt ((mul_le_mul_of_nonneg_left (hbound i)
    (div_nonneg hε.le hC1.le)).trans_lt hfrac)

end SurveyStatements.P5OperatorReduction
