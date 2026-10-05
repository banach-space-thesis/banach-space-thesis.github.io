import ThesisCommon.Analysis.L1SeparableEnvelope
import ThesisCommon.Analysis.L1SubsigmaProjection

/-! The complemented-space assertion accompanying Proposition 3.9. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS

/-- The finite-measure separable envelope has an actual contractive
conditional-expectation projection. Zero measures are included. -/
theorem separable_L1_complemented_envelope {X : Type*} {m₀ : MeasurableSpace X}
    (μ : @Measure X m₀) [IsFiniteMeasure μ]
    (M : Set (Lp ℝ 1 μ)) (hM : TopologicalSpace.IsSeparable M) :
    ∃ (m : MeasurableSpace X) (_hm : m ≤ m₀) (Q : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ),
      @MeasurableSpace.CountablyGenerated X m ∧ M ⊆ lOneSubsigma μ m ∧
      Set.range Q = (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) ∧ Q.comp Q = Q ∧ ‖Q‖ ≤ 1 := by
  obtain ⟨m, hm, hmc, hMm⟩ := exists_countablyGenerated_lOneSubsigma μ M hM
  exact ⟨m, hm, lOneSubsigmaProjection μ hm, hmc, hMm,
    range_lOneSubsigmaProjection μ hm, lOneSubsigmaProjection_idempotent μ hm,
    norm_lOneSubsigmaProjection_le μ hm⟩

end PEMS
