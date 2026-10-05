import ThesisCommon.Analysis.IntervalUpperDichotomy
import ThesisCommon.Analysis.IntervalSmallBlocks

/-! The unit-interval topological, backward and upper-dichotomy dependencies.
The ordinal alternative remains a separate obligation.
The extension theorem here is the nonempty subinterval case actually used
in the proof, as in Remark 2.16, not arbitrary closed-set Dugundji extension. -/
namespace LPCK
alias lemma_2_14 := ThesisCommon.unitInterval_closed_cover_contains_copy
alias remark_2_16_extension_norm := ThesisCommon.norm_unitIntervalExtend
alias remark_2_16_extension_identity := ThesisCommon.unitIntervalRestrict_comp_extend
alias lemma_3_11_unitInterval := ThesisCommon.interval_lp_backward_reduction
alias proposition_3_13_unitInterval := ThesisCommon.interval_lp_lower_triangular
alias proposition_3_15_unitInterval := ThesisCommon.interval_lp_upper_dichotomy
alias lemma_4_1_unitInterval := ThesisCommon.interval_infinity_forward_reduction
end LPCK
