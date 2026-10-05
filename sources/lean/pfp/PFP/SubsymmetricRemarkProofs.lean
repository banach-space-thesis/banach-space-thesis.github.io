import ThesisCommon.Analysis.SubsymmetricBasisPFP

/-! Remark 3.4: the non-ell-one subsymmetric extension of Theorem 3.3.
The finite coefficient formulation retains arbitrary unconditional and
subsequence constants. Its proof gives 4 K^2 C^2-PFP in the original norm;
no endpoint 2-PFP assertion is made for a general subsymmetric norm. -/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

def Remark_3_4 (b : NormalizedSchauderBasis 𝕜 X) : Prop :=
  b.IsSubsymmetric → ¬ b.EquivalentEllOne → HasUPFP 𝕜 X

theorem remark_3_4 (b : NormalizedSchauderBasis 𝕜 X) : Remark_3_4 𝕜 X b :=
  b.hasUPFP_of_subsymmetric

end PFP
