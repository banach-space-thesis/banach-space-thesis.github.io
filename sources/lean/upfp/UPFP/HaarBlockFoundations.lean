import ThesisCommon.Analysis.LpMeanZeroHaarBasis
import ThesisCommon.Analysis.LpHaarParentSelection
import ThesisCommon.Analysis.HaarTraceSignBalancing
import ThesisCommon.Analysis.LpHaarDyadicTraceAlgebra
import ThesisCommon.Analysis.SchauderStableOperatorLimit
import ThesisCommon.Analysis.SchauderSummableScalar
import ThesisCommon.Analysis.LpPartitionNormTransfer
import ThesisCommon.Analysis.ScalarCompressionCriterion
import ThesisCommon.Analysis.IntervalLpUniformFactorization

/-! Checked foundations for the Alspach--Enflo--Odell route in genuine
interval Lp, over real and complex scalars. These include actual mean-zero
retractions, two-sided finite block selection, trace limits and norm bounds.

The infinite faithful block retractions, normalized arbitrary-operator
diagonal reduction and multiplier scalar stabilization are constructed.
IntervalLpUniformFactorization proves the actual finite-p base UPFP. -/
