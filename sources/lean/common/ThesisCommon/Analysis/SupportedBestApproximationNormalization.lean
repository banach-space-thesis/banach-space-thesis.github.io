import ThesisCommon.Analysis.SupportedBestApproximationTransport
import ThesisCommon.Analysis.LocalizedProbabilityDensity

/-! Conditional normalization of a sigma-finite output support. An actual
best-approximation theorem for finite localizations of the output measure
transfers to the original sigma-finite support. This lemma isolates only
the change-of-density step; it does not assume or assert global attainment. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MeasurableSpace Y] {ν : Measure Y}

theorem exists_supported_bestApproximation_sigmaFinite_of_finite
    (Θ : Set Y) (hΘ : MeasurableSet Θ) [SigmaFinite (ν.restrict Θ)]
    (T : E →L[𝕜] Lp 𝕜 1 ν)
    (hfinite : ∀ ν' : Measure Y, IsFiniteMeasure (ν'.restrict Θ) →
      ∀ R : E →L[𝕜] Lp 𝕜 1 ν', ∃ W : E →L[𝕜] Lp 𝕜 1 ν',
        IsWeaklyCompactOperator W ∧ L1OperatorSupportedOn Θ W ∧
          ‖R - W‖ = supportedWeakEssentialNorm Θ R) :
    ∃ W : E →L[𝕜] Lp 𝕜 1 ν, IsWeaklyCompactOperator W ∧ L1OperatorSupportedOn Θ W ∧
      ‖T - W‖ = supportedWeakEssentialNorm Θ T := by
  obtain ⟨g, C, hg, hpos, _, _, hfin, _⟩ := exists_localized_probability_density ν Θ hΘ
  let ν' := ν.withDensity (fun y => (g y : ℝ≥0∞))
  have hν' : IsFiniteMeasure (ν'.restrict Θ) := isFiniteMeasure_restrict.mpr hfin.ne
  let e := lOneWithDensityEquiv_rclike (𝕜 := 𝕜) hg hpos
  let R := e.symm.toLinearIsometry.toContinuousLinearMap.comp T
  have heq : e.toLinearIsometry.toContinuousLinearMap.comp R = T := by
    apply ContinuousLinearMap.ext
    intro f
    exact e.apply_symm_apply (T f)
  have h := exists_supported_bestApproximation_postcomp_isometry e Θ
    (lOneWithDensityEquiv_supported_iff hg hpos Θ hΘ) R (hfinite ν' hν' R)
  simpa only [heq] using h

end ThesisCommon
