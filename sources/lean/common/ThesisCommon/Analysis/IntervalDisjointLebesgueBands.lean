import ThesisCommon.Analysis.IntervalDisjointLebesgueMeasures
import ThesisCommon.Analysis.ContinuousMapComplexPrincipalL1Equiv

/-! The disjoint vertical-fibre measures give genuine pairwise disjoint
principal bands in the interval dual. Each real or complex band is Lebesgue L1. -/
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace ThesisCommon.IntervalDisjointLebesgue
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice

def generator (t : unitInterval) : C(unitInterval, ℝ) →L[ℝ] ℝ :=
  continuousMapIntegralCLM (measure t)

theorem generator_nonneg (t : unitInterval) : 0 ≤ generator t :=
  continuousMapIntegralCLM_nonneg (measure t)

theorem generator_disjoint : Pairwise (fun s t => |generator s| ⊓ |generator t| = 0) := by
  intro s t h
  rw [abs_of_nonneg (generator_nonneg s), abs_of_nonneg (generator_nonneg t)]
  apply (positiveContinuousMapRiesz_mutuallySingular_iff _ _
    (generator_nonneg s) (generator_nonneg t)).mp
  simpa only [generator, positiveContinuousMapRiesz_integral] using mutuallySingular h

def realBandEquiv (t : unitInterval) :
    IntervalLp ℝ ⟨1, le_rfl⟩ ≃ₗᵢ[ℝ] principalBand (generator t) := by
  have e := continuousMapPrincipalL1Equiv (generator t) (generator_nonneg t)
  have hm : positiveContinuousMapRiesz (generator t) (generator_nonneg t) = measure t :=
    positiveContinuousMapRiesz_integral (measure t)
  rw [hm] at e
  have e' : Lp ℝ 1 (measure t) ≃ₗᵢ[ℝ] principalBand (generator t) := by
    exact e
  exact (l1Equiv ℝ t).symm.trans e'

def complexBandEquiv (t : unitInterval) :
    IntervalLp ℂ ⟨1, le_rfl⟩ ≃ₗᵢ[ℂ] continuousMapComplexPrincipalBand (generator t) := by
  have e := continuousMapComplexPrincipalL1Equiv (generator t) (generator_nonneg t)
  have hm : positiveContinuousMapRiesz (generator t) (generator_nonneg t) = measure t :=
    positiveContinuousMapRiesz_integral (measure t)
  rw [hm] at e
  have e' : Lp ℂ 1 (measure t) ≃ₗᵢ[ℂ] continuousMapComplexPrincipalBand (generator t) := by
    exact e
  exact (l1Equiv ℂ t).symm.trans e'

end ThesisCommon.IntervalDisjointLebesgue
