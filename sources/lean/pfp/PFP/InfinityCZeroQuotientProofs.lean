import PFP.QuotientStatements
import ThesisCommon.Analysis.InfinityQuotientPFP

/-! Full Proposition 5.1 with its printed endpoint constant two. -/
noncomputable section
namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem proposition_5_1 : Proposition_5_1 𝕜 := infinityCZeroQuotient_hasCPFP_two

end PFP
