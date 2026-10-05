import ThesisCommon.Analysis.PositiveLinearMapBounded
import ThesisCommon.Analysis.L1OperatorModulus

/-! The two directions of B(L1,L1)=L_r(L1,L1), quantified over algebraic
linear maps. Regularity does not include continuity in its definition. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lOne_linearMap_continuous_iff_regular (T : Lp ℝ 1 μ →ₗ[ℝ] Lp ℝ 1 ν) :
    Continuous T ↔ IsRegularLinearMap T := by
  constructor
  · intro hT
    obtain ⟨P, Q, hP, hQ, heq⟩ := lOne_operator_regular (⟨T, hT⟩ : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    exact ⟨P.toLinearMap, Q.toLinearMap, hP, hQ, congrArg ContinuousLinearMap.toLinearMap heq⟩
  · exact continuous_regular_linearMap T

end ThesisCommon
