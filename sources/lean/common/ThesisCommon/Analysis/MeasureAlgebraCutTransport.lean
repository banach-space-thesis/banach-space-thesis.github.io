import ThesisCommon.Analysis.MeasureAlgebraBandTransport

/-! Actual output cutoffs under arbitrary finite measure-algebra transport.
The representative set is supplied by the measure-algebra isomorphism;
no underlying point map or countability assumption is needed. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
variable {X Y X' Y' : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
variable {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
variable (Φ : MeasureAlgebraIso μ μ') (Ψ : MeasureAlgebraIso ν ν')

theorem measureAlgebraOperatorEquiv_outputCut (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (B : Set Y) (hB : MeasurableSet B) :
    measureAlgebraOperatorEquiv Φ Ψ ((lpCutL B hB).comp T) =
      (lpCutL (Ψ.imageSet B hB) (Ψ.measurableSet_imageSet B hB)).comp
        (measureAlgebraOperatorEquiv Φ Ψ T) := by
  apply ContinuousLinearMap.ext
  intro f
  change Ψ.lOneEquiv (lpCut B hB (T (Φ.lOneEquiv.symm f))) =
    lpCut (Ψ.imageSet B hB) (Ψ.measurableSet_imageSet B hB)
      (Ψ.lOneEquiv (T (Φ.lOneEquiv.symm f)))
  exact Ψ.lOneEquiv_cut B hB _

theorem norm_measureAlgebraOperatorEquiv_outputCut (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (B : Set Y) (hB : MeasurableSet B) :
    ‖(lpCutL (Ψ.imageSet B hB) (Ψ.measurableSet_imageSet B hB)).comp
      (measureAlgebraOperatorEquiv Φ Ψ T)‖ = ‖(lpCutL B hB).comp T‖ := by
  rw [← measureAlgebraOperatorEquiv_outputCut Φ Ψ T B hB]
  exact (measureAlgebraOperatorEquiv Φ Ψ).norm_map _

end ThesisCommon
