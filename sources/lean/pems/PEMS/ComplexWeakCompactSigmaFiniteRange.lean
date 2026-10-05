import ThesisCommon.Analysis.ComplexWeakCompactL1SigmaFiniteRange

/-! The complex form of source Proposition 4.21. There is no condition
on the output measure and no restriction on the complex source space. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS

theorem proposition_4_21_complex {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace Y]
    {ν : Measure Y} {T : E →L[ℂ] Lp ℂ 1 ν} (hT : IsWeaklyCompactOperator T) :
    ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧
      ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0 := by
  letI : Module ℝ E := RestrictScalars.module ℝ ℂ E
  letI : IsScalarTower ℝ ℂ E := RestrictScalars.isScalarTower _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  exact hT.exists_sigmaFinite_range_part_complex

end PEMS
