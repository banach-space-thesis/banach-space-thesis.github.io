import ThesisCommon.Analysis.IntegralOperatorBand
import ThesisCommon.Analysis.LatticeDisjointness

/-! The equivalent signed-modulus criterion for singular operators and
the modulus of the actual integral/singular decomposition. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem isSingularOperator_iff_abs_sub_eq_abs_add (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsSingularOperator S ↔ ∀ K, IsIntegralOperator K → |S - K| = |S + K| := by
  constructor
  · intro hS K hK
    exact (lattice_abs_inf_abs_eq_zero_iff S K).mp (hS K hK)
  · intro hS K hK
    exact (lattice_abs_inf_abs_eq_zero_iff S K).mpr (hS K hK)

theorem singular_integral_abs_add {S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : IsSingularOperator S) (hK : IsIntegralOperator K) : |S + K| = |S| + |K| :=
  lattice_abs_add_of_disjoint (hS K hK)

theorem singular_integral_abs_sub {S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : IsSingularOperator S) (hK : IsIntegralOperator K) : |S - K| = |S| + |K| :=
  lattice_abs_sub_of_disjoint (hS K hK)

variable [SigmaFinite μ] [SigmaFinite ν]

theorem integral_singular_modulus_decomposition (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    |T| = |T - integralBandProjection T| + |integralBandProjection T| := by
  have h := singular_integral_abs_add (integralBandProjection_residual_singular T)
    (integralBandProjection_isIntegral T)
  simpa only [sub_add_cancel] using h

theorem norm_integral_singular_decomposition (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ‖T‖ = ‖|T - integralBandProjection T| + |integralBandProjection T|‖ := by
  rw [← integral_singular_modulus_decomposition, norm_abs_lOneOperator]

end ThesisCommon
