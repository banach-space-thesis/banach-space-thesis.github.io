import ThesisCommon.Analysis.CompactUpperTriangular
import ThesisCommon.Analysis.CZeroLpForward
import ThesisCommon.Analysis.CZeroLpUpperTriangular

/-! Source-numbered forward reductions. Lemmas 3.1--3.3 and Proposition
3.5 are proved here for the actual finite-p sums needed by the main results;
the manuscript's more general unconditional E-sum version is not claimed.
The compactness hypothesis remains exactly the hypothesis of these lemmas.
Its ordinal C(K) instance (Proposition 3.6) is a separate open dependency. -/
namespace LPCK
alias lemma_3_1_lp := ThesisCommon.lp_coordinate_norm_tendsto_zero_of_scalar_compact
alias corollary_3_2_lp := ThesisCommon.lp_strong_forward_of_scalar_compact
alias lemma_3_3_lp := ThesisCommon.lp_forward_column_selection_of_scalar_compact
alias proposition_3_5_lp := ThesisCommon.lp_upper_triangular_of_scalar_compact
alias lemma_3_8 := ThesisCommon.cZero_to_lp_forward_coordinate
alias lemma_3_10 := ThesisCommon.lp_cZero_upper_triangular
end LPCK
