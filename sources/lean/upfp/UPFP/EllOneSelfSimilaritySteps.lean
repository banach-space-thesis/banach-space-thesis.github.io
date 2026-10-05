import UPFP.MainStatements
import ThesisCommon.Analysis.EllOneForwardSelection
import ThesisCommon.Analysis.EllOneBackwardSelection

/-! Source-numbered exports for the ell1 self-similarity reductions.
For finite p, 1 < p.toReal expresses 1 < p < infinity. The infinite-p and
c0 cases are separate. All maps are actual coordinate restrictions and
insertions, and every embedding has an infinite range. The recursive
exports allow arbitrary positive tolerances, strengthening the manuscript's
geometric choices epsilon/2^(j+1). -/
namespace UPFP

alias lemma_3_2_lp := ThesisCommon.lp_to_ellOne_forward_reduction
alias lemma_3_2_infinity := ThesisCommon.infinity_to_ellOne_forward_reduction
alias lemma_3_2_cZero := ThesisCommon.cZero_to_ellOne_forward_reduction
alias lemma_4_4_lp := ThesisCommon.lp_to_ellOne_backward_reduction
alias lemma_4_4_infinity := ThesisCommon.infinity_to_ellOne_backward_reduction
alias lemma_4_4_cZero := ThesisCommon.cZero_to_ellOne_backward_reduction
alias proposition_3_3_lp := ThesisCommon.ellOne_lp_forward_selection
alias proposition_3_3_cZero := ThesisCommon.ellOne_cZero_forward_selection
alias proposition_4_5_lp := ThesisCommon.ellOne_lp_backward_selection
alias proposition_4_5_cZero := ThesisCommon.ellOne_cZero_backward_selection

end UPFP
