import PEMS.MeasureDefinitions
import ThesisCommon.Analysis.SigmaMeasurePartition

/-! A coproduct of arbitrary finite measure spaces satisfies the exact
strict localizability definition, including piecewise measurability. -/
noncomputable section
open MeasureTheory Set ThesisCommon
namespace PEMS
variable {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)]

theorem sigmaMeasure_strictlyLocalizable (μ : ∀ i, Measure (X i))
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, Nonempty (X i)] : StrictlyLocalizable (sigmaMeasure μ) := by
  let parts : Set (Set (Sigma X)) := range sigmaMeasureFiber
  let e : I ≃ parts := Equiv.ofInjective sigmaMeasureFiber sigmaMeasureFiber_injective
  refine ⟨parts, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨i, rfl⟩
    exact ⟨sigmaMeasureFiber_measurable i, by rw [sigmaMeasure_fiber]; exact measure_lt_top _ _⟩
  · rintro A ⟨i, rfl⟩ B ⟨j, rfl⟩ hne
    exact sigmaMeasureFiber_disjoint (fun h => hne (h ▸ rfl))
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨sigmaMeasureFiber x.1, ⟨x.1, rfl⟩, x.2, rfl⟩
  · intro A
    constructor
    · intro hA B hB
      obtain ⟨i, rfl⟩ := hB
      exact hA.inter (sigmaMeasureFiber_measurable i)
    · intro h
      apply (sigmaSet_measurable_iff A).mpr
      intro i
      have hi : Sigma.mk i ⁻¹' (A ∩ sigmaMeasureFiber i) = Sigma.mk i ⁻¹' A := by
        ext x
        simp [sigmaMeasureFiber]
      simpa only [hi] using (measurable_sigmaMk i) (h _ ⟨i, rfl⟩)
  · intro A hA
    calc
      sigmaMeasure μ A = ∑' i, sigmaMeasure μ (A ∩ sigmaMeasureFiber i) := by
        have hh := congrArg (fun m : Measure (Sigma X) => m A) (sigmaMeasure_sum_restrict μ)
        simpa only [Measure.sum_apply _ hA, Measure.restrict_apply hA] using hh.symm
      _ = ∑' B : parts, sigmaMeasure μ (A ∩ B.val) := e.tsum_eq (fun B : parts => sigmaMeasure μ (A ∩ B.val))

end PEMS
