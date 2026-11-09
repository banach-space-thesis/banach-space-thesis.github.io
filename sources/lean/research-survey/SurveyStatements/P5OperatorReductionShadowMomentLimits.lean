import SurveyStatements.P5OperatorReductionDisjointMoments
import SurveyStatements.P5OperatorReductionVarianceLimits

/-! Uniform small-cell signed moments pass to all scalar limits along
the same reservoir. This is used for the pre-registered traces of every
finite sign choice in the alternating construction. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
open SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem limiting_restricted_reader_signed_variance_small
    (y : ℕ → Lp 𝕜 1 unitIntervalMeasure) (hy : UniformSmallRestrictions y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ m, ‖y m‖ ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, ∀ s : Fin n → Set ℝ, ∀ hs : ∀ j, MeasurableSet (s j),
      (∀ j k, j ≠ k → Disjoint (s j) (s k)) →
      (∀ j, unitIntervalMeasure (s j) ≤ ENNReal.ofReal δ) →
      ∀ φ : Fin n → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜,
      (∀ j, ‖φ j‖ ≤ 1) → ∀ a : (Fin n → Bool) → 𝕜,
      (∀ θ : Fin n → Bool, Tendsto (fun m : ℕ => ∑ j : Fin n,
        signedValue (θ j) (restrictedFunctional (𝕜 := 𝕜) (s j) (hs j) (φ j) (y m)))
          atTop (𝓝 (a θ))) →
      mean (fun θ : Fin n → Bool => ‖a θ‖ ^ 2) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := uniform_restricted_reader_signed_variance_small
    y hy hC hbound (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun n s hs hd hμ φ hφ a ha => ?_⟩
  have hb : mean (fun θ => ‖a θ‖ ^ 2) ≤ ε / 2 :=
    signed_second_moment_bound_of_limit
      (fun (m : ℕ) (θ : Fin n → Bool) => ∑ j : Fin n, signedValue (θ j)
        (restrictedFunctional (𝕜 := 𝕜) (s j) (hs j) (φ j) (y m))) a ha
      (Eventually.of_forall (fun m => (hsmall n s hs hd hμ φ hφ m).le))
  exact hb.trans_lt (by linarith)

end SurveyStatements.P5OperatorReduction
