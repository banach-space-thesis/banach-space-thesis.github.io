import ThesisCommon.Analysis.L1SeparableEnvelope

/-! The finite-measure separable envelope of Proposition 3.9. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS

/-- Proposition 3.9, finite-measure assertion: a separable subset lies in
the actual closed separable L1 sublattice of a countably generated
sub-sigma-algebra. Its trimmed L1 realization is `lOneSubsigmaEmbedding`. -/
theorem separable_L1_subsigma_envelope {X : Type*} {m₀ : MeasurableSpace X}
    (μ : @Measure X m₀) [IsFiniteMeasure μ]
    (M : Set (Lp ℝ 1 μ)) (hM : TopologicalSpace.IsSeparable M) :
    ∃ (m : MeasurableSpace X) (_hm : m ≤ m₀), @MeasurableSpace.CountablyGenerated X m ∧
      M ⊆ lOneSubsigma μ m ∧ IsClosed (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) ∧
      TopologicalSpace.IsSeparable (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) :=
  exists_closed_separable_lOneSubsigma μ M hM

end PEMS
