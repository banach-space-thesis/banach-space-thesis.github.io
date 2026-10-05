import ThesisCommon.Analysis.InfinityCZeroQuotient
import ThesisCommon.Analysis.QuantitativePrimary

/-! The exact endpoint assertion of Proposition 5.1 on the actual quotient
Banach space. This target is a specification, not a proof. -/
noncomputable section
namespace PFP
open ThesisCommon

/-- Proposition 5.1, `prop: l_infty-quot-c0`, with its endpoint constant two. -/
def Proposition_5_1 (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  HasCPFP 𝕜 (InfinityCZeroQuotient 𝕜) 2

end PFP
