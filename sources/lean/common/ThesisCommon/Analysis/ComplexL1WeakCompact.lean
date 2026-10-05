import ThesisCommon.Analysis.WeakCompactRestrictScalars
import ThesisCommon.Analysis.ComplexL1OperatorPhases

/-! Genuine weak compactness of complex L1 operators is equivalent to
weak compactness of both real coordinates. Complexification preserves and
reflects it, using equality of the real and complex weak topologies. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem IsWeaklyCompactOperator.complexL1Extension
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsWeaklyCompactOperator S) :
    IsWeaklyCompactOperator (complexL1Extension S) := by
  apply IsWeaklyCompactOperator.of_restrictScalars_real
  change IsWeaklyCompactOperator (complexL1ExtensionReal S)
  have hr := (hS.comp_right (complexL1Re μ)).comp_left (complexL1OfReal ν)
  have hi := (hS.comp_right (complexL1Im μ)).comp_left (complexL1OfReal ν)
  have his : IsWeaklyCompactOperator
      (Complex.I • (complexL1OfReal ν).comp (S.comp (complexL1Im μ))) := by
    simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using
      hi.comp_left (Complex.I • ContinuousLinearMap.id ℝ (Lp ℂ 1 ν))
  exact hr.add his

theorem IsWeaklyCompactOperator.complexL1OperatorRe
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν} (hT : IsWeaklyCompactOperator T) :
    IsWeaklyCompactOperator (complexL1OperatorRe T) :=
  (hT.restrictScalars_real.comp_right (complexL1OfReal μ)).comp_left (complexL1Re ν)

theorem IsWeaklyCompactOperator.complexL1OperatorIm
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν} (hT : IsWeaklyCompactOperator T) :
    IsWeaklyCompactOperator (complexL1OperatorIm T) :=
  (hT.restrictScalars_real.comp_right (complexL1OfReal μ)).comp_left (complexL1Im ν)

theorem weaklyCompact_complexL1Extension_iff (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsWeaklyCompactOperator (complexL1Extension S) ↔ IsWeaklyCompactOperator S := by
  constructor
  · intro h
    simpa only [complexL1OperatorRe_extension] using h.complexL1OperatorRe
  · exact IsWeaklyCompactOperator.complexL1Extension

theorem weaklyCompact_complexL1_components_iff (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    IsWeaklyCompactOperator T ↔ IsWeaklyCompactOperator (complexL1OperatorRe T) ∧
      IsWeaklyCompactOperator (complexL1OperatorIm T) := by
  constructor
  · exact fun h => ⟨h.complexL1OperatorRe, h.complexL1OperatorIm⟩
  · rintro ⟨hr, hi⟩
    have h := hr.complexL1Extension.add (hi.complexL1Extension.smul Complex.I)
    change IsWeaklyCompactOperator (complexL1Extension ((complexL1Re ν).comp (complexL1OperatorRealRestriction T)) + Complex.I • complexL1Extension ((complexL1Im ν).comp (complexL1OperatorRealRestriction T))) at h
    rwa [← complexL1Operator_decomposition T] at h

end ThesisCommon
