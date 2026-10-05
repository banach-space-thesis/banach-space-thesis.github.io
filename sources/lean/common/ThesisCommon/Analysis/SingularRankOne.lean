import ThesisCommon.Analysis.IntegralPrincipalBand
import ThesisCommon.Analysis.IntegralSingularModulus
import ThesisCommon.Analysis.ALRefinementPrincipal

/-! On finite real measure spaces, singularity can be tested against the
actual constant-kernel rank-one operator. This uses the proved principal-band
characterization of all integral operators. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem isSingularOperator_iff_disjoint_rankOne (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsSingularOperator S ↔ |S| ⊓ integralRankOne μ ν = 0 := by
  constructor
  · intro hS
    simpa only [abs_of_nonneg integralRankOne_nonneg] using
      hS (integralRankOne μ ν) integralRankOne_isIntegral
  · intro hS
    have hmem : integralRankOne μ ν ∈ latticeDisjointComplement {S} := by
      intro T hT
      have hTS : T = S := hT
      simpa only [hTS, abs_of_nonneg integralRankOne_nonneg, inf_comm] using hS
    have hle := integralOperatorSubmodule_le_of_rankOne_mem
      (latticeDisjointComplement_orderClosed {S}) hmem
    intro K hK
    have h := hle hK S (mem_singleton S)
    simpa only [inf_comm] using h

theorem isSingularOperator_iff_abs_sub_rankOne_eq_abs_add
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsSingularOperator S ↔
      |S - integralRankOne μ ν| = |S + integralRankOne μ ν| := by
  rw [isSingularOperator_iff_disjoint_rankOne]
  simpa only [abs_of_nonneg integralRankOne_nonneg] using
    lattice_abs_inf_abs_eq_zero_iff S (integralRankOne μ ν)

end ThesisCommon
