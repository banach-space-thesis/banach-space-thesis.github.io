import PFP.GeneralSumBlockStatements
import ThesisCommon.Analysis.CountableLpBlocks
import ThesisCommon.Analysis.WCGEllOneSupport

/-! Full Lemma 4.24. WCG support reduction feeds the actual first-unused
ordinal construction; block invariance and compression idempotence follow
from the genuine lp finite-sum expansion. No invariance premise is assumed. -/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem lemma_4_24 : Lemma_4_24 𝕜 Γ X := by
  classical
  intro hX P hP
  have hs (α : Γ) := hX.ellOne_operator_countable_support
    (P.comp (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := 1) (E := fun _ : Γ => X) α))
  choose F hF hPF using hs
  exact exists_lp_triangular_countable_blocks 1 (by norm_num) P hP F hF
    (fun α x β hβ => by
      simpa only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
        using hPF α x β hβ)

end PFP
