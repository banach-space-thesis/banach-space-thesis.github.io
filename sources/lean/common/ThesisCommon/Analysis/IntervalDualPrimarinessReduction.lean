import ThesisCommon.Analysis.IntervalDualRepresentation
import ThesisCommon.Analysis.WCGEllOnePrimaryTransfer
import ThesisCommon.Analysis.SeparableWeaklyCompactlyGenerated
import ThesisCommon.Analysis.ContinuumScheduling
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! All structural inputs in the interval-dual primariness application are
proved here. The independent primariness theorem for actual Lebesgue L1
remains an explicit premise. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace ThesisCommon
open TopologicalSpace

theorem intervalContinuousDual_isPrimary_of_lebesgueL1_isPrimary
    (𝕜 : Type*) [RCLike 𝕜]
    (hCH : (Cardinal.aleph 1 : Cardinal.{0}) < Cardinal.continuum)
    (hL1 : IsPrimary 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩)) :
    IsPrimary 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := by
  have hcard : Cardinal.mk UnitInterval = Cardinal.continuum :=
    Cardinal.mk_Icc_real (show (0 : ℝ) < 1 from zero_lt_one)
  letI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SeparableSpace (IntervalLp 𝕜 ⟨1, le_rfl⟩) := by
    change SeparableSpace (MeasureTheory.Lp 𝕜 1
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
    infer_instance
  have hX := isWeaklyCompactlyGenerated_of_separable 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩)
  have hcount := hL1.of_equiv
    (intervalLpFunctionSelfSimilarity 𝕜 ⟨1, le_rfl⟩ (by simp)).toContinuousLinearEquiv
  have hlarge : Cardinal.aleph 1 < Cardinal.mk UnitInterval := by rwa [hcard]
  have hcof : Cardinal.aleph0 < (Cardinal.mk UnitInterval).ord.cof := by
    rw [hcard]
    exact aleph0_lt_cof_continuum
  exact (hX.ellOne_isPrimary_of_countable_model hlarge hcof hcount).of_equiv
    (intervalContinuousDualLebesgueEquiv 𝕜).symm

end ThesisCommon
