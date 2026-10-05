import ThesisCommon.Analysis.WeakCompactL1SigmaFiniteRange

/-! The real-scalar form of Proposition 4.21, without any localizability
assumption on the output measure or any restriction on the source space. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS

theorem proposition_4_21_real {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Y]
    {ν : Measure Y} {T : E →L[ℝ] Lp ℝ 1 ν} (hT : IsWeaklyCompactOperator T) :
    ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧
      ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0 :=
  hT.exists_sigmaFinite_range_part

end PEMS
