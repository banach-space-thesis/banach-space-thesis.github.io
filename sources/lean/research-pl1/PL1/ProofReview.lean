import PL1.PartialMainTheorems
import PL1.DyadicTrace
import PL1.FiniteDimensionalRNP
import PL1.MetricApproximation
import PL1.IntrinsicNonBoundedComplete
import PL1.BochnerResolvents
import PL1.SchurLattice
import PL1.LatticeDisjointCountability
import PL1.OperatorDomination
import PL1.LpOperatorLift
import PL1.HilbertTraceBounds
import PL1.SmoothingApproximation
import PL1.IntervalEll1Obstruction
import PL1.ScalarUnconditionalRNP
import PL1.MatrixSmoothing
import PL1.LatticeReduction

/-! # Exact result and axiom inspection for the three-hour construction

This review retains the first pass's partial endpoints, with concrete interval
witnesses and no assumed analytic construction hypotheses. The full A proof
and subsequent results are inspected in `PL1.SecondProofReview`; full B remains
conditional on explicit structural results.
-/

set_option pp.universes true

#check @PL1.theoremA_except_nonlattice
#check @PL1.theoremB_partial
#check PL1.theoremA_except_nonlattice ℝ
#check PL1.theoremA_except_nonlattice ℂ
#check PL1.theoremB_partial ℝ
#check PL1.theoremB_partial ℂ

#print axioms PL1.theoremA_except_nonlattice
#print axioms PL1.theoremB_partial
#print axioms PL1.Noise.schurRates_projection_range_underlyingReal_hasSchurProperty
#print axioms PL1.Noise.projection_range_underlyingReal_separableSpace
#print axioms PL1.RNPBridge.hasRadonNikodymProperty_of_finiteDimensional
#print axioms PL1.RNPTransport.hasRadonNikodymProperty_restrictScalars_iff
#print axioms PL1.ContractiveRetract.norm_transport_le
#print axioms PL1.ContractiveRetract.rangeEquiv_norm

#check @PL1.DyadicTrace.trace
#check @PL1.DyadicTrace.norm_trace_le
#check @PL1.DyadicTrace.trace_id
#check @PL1.DyadicTrace.one_le_norm_id_sub
#print axioms PL1.DyadicTrace.norm_trace_le
#print axioms PL1.DyadicTrace.trace_id
#print axioms PL1.DyadicTrace.one_le_norm_id_sub

#check @PL1.Noise.intrinsic_hasMetricApproximationProperty
#check @PL1.Noise.finrank_intrinsicExpectation
#check @PL1.Noise.finrank_intrinsicBlock
#check @PL1.Noise.intrinsicBlock_expansion_unique
#check @PL1.Noise.schur_intrinsic_exists_nonCauchy_branch
#check @PL1.Noise.constant_intrinsic_exists_nonCauchy_branch
#check PL1.Noise.schur_intrinsic_exists_nonCauchy_branch ℂ
#check PL1.Noise.constant_intrinsic_exists_nonCauchy_branch ℂ
#check @PL1.ScalarDecompositionRNP.hasRNP_of_scalar_projections
#check @PL1.UnconditionalRNP.hasRadonNikodymProperty_of_schur_unconditional_projections
#check @PL1.Noise.resolventL1_eq_integral
#check @PL1.Noise.norm_resolventL1_sub_truncated_le

#print axioms PL1.Noise.intrinsic_hasMetricApproximationProperty
#print axioms PL1.Noise.norm_intrinsicExpectation_eq_one
#print axioms PL1.Noise.finrank_intrinsicExpectation
#print axioms PL1.Noise.finrank_intrinsicBlock
#print axioms PL1.Noise.intrinsicBlock_comp
#print axioms PL1.Noise.intrinsicBlock_expansion_unique
#print axioms PL1.Noise.tendsto_intrinsicBlock_partialSum
#print axioms PL1.Noise.schur_intrinsic_not_boundedlyComplete
#print axioms PL1.Noise.constant_intrinsic_not_boundedlyComplete
#print axioms PL1.Noise.schur_intrinsic_exists_nonCauchy_branch
#print axioms PL1.Noise.constant_intrinsic_exists_nonCauchy_branch
#print axioms PL1.Noise.schur_intrinsic_no_uniform_sign_bound
#print axioms PL1.DecompositionRNP.hasRadonNikodymProperty_of_boundedlyCompleteDecomposition
#print axioms PL1.ScalarDecompositionRNP.hasRNP_of_scalar_projections
#print axioms PL1.UnconditionalRNP.hasRadonNikodymProperty_of_schur_unconditional_projections
#print axioms PL1.Noise.noiseL1_add
#print axioms PL1.Noise.continuous_noiseL1_apply
#print axioms PL1.Noise.resolventL1_strong_zero
#print axioms PL1.Noise.resolventL1_eq_integral
#print axioms PL1.Noise.norm_resolventL1_sub_truncated_le
#print axioms PL1.Noise.truncatedResolventL1_tendsto
#print axioms PL1.SchurLattice.tendsto_zero_of_antitone_net_isGLB
#print axioms PL1.SchurLattice.conditionallyCompleteLattice
#print axioms PL1.SchurLattice.exists_countable_maximal_disjoint_positive_family
#print axioms PL1.OperatorDomination.exists_measurable_dominator
#print axioms PL1.OperatorDomination.cutoff_approximation
#print axioms PL1.OperatorDomination.maskedRestrictionLp
#print axioms PL1.LpInterpolation.norm_toLp_le_of_ae_norm_bound
#print axioms PL1.HilbertTraceBounds.sum_cell_dual_norm_sq_le
#print axioms PL1.HilbertTraceBounds.norm_sum_cell_apply_le

#check @PL1.SmoothingTrace.trace_tendsto_zero_of_smoothing
#check @PL1.SmoothingTrace.one_le_norm_id_sub_of_smoothing
#check @PL1.SmoothingTrace.trace_tendsto_zero_of_smoothing_approximation
#check @PL1.SmoothingTrace.one_le_norm_id_sub_of_smoothing_approximation
#print axioms PL1.SmoothingTrace.trace_tendsto_zero_of_smoothing
#print axioms PL1.SmoothingTrace.one_le_norm_id_sub_of_smoothing
#print axioms PL1.SmoothingTrace.trace_tendsto_zero_of_smoothing_approximation
#print axioms PL1.SmoothingTrace.one_le_norm_id_sub_of_smoothing_approximation

#check @PL1.Ell1RNP.hasRadonNikodymProperty
#check PL1.Noise.schur_intervalProjection_range_not_isomorphic_ell1 ℂ
#check PL1.Noise.constant_intervalProjection_range_not_isomorphic_ell1 ℂ
#print axioms PL1.Ell1RNP.hasRadonNikodymProperty
#print axioms PL1.Noise.schur_intervalProjection_range_not_isomorphic_ell1
#print axioms PL1.Noise.constant_intervalProjection_range_not_isomorphic_ell1

#check PL1.Noise.schur_intrinsic_no_uniform_scalar_sign_bound ℂ
#print axioms PL1.Noise.schur_intrinsic_no_uniform_scalar_sign_bound

#check @PL1.InputCompression.norm_input_compression_error_tendsto_zero
#check @PL1.OutputCompression.tendsto_output_compression
#check @PL1.MatrixTrace.trace_tendsto_zero_of_smoothing_entries
#check @PL1.MatrixTrace.one_le_norm_id_sub_of_smoothing_entries
#print axioms PL1.InputCompression.norm_input_compression_error_tendsto_zero
#print axioms PL1.OutputCompression.tendsto_output_compression
#print axioms PL1.MatrixTrace.trace_tendsto_zero_of_smoothing_entries
#print axioms PL1.MatrixTrace.one_le_norm_id_sub_of_smoothing_entries

#check @PL1.hasEquivalentRealLatticeNorm_iff_hasBanachLatticeModel
#print axioms PL1.hasEquivalentRealLatticeNorm_iff_hasBanachLatticeModel

-- This reduction remains conditional in its type. `PL1.MainTheoremA` now
-- discharges the premise; an axiom list alone does not discharge a parameter.
#print PL1.SeparableSchurLatticeRNP
#check @PL1.theoremA_of_separableSchurLatticeRNP
#print axioms PL1.theoremA_of_separableSchurLatticeRNP
