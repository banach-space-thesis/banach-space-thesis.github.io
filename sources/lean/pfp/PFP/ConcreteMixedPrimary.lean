import PFP.MainStatements
import ThesisCommon.Analysis.ConcreteMixedPrimary

/-! The full primariness corollaries, on the original concrete sequence
spaces. The proofs use the mixed factorisation results and the explicit
countable-sum self-similarity in Pełczyński's decomposition method. -/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

theorem corollary_3_16 : Corollary_3_16 𝕜 := by
  refine ⟨cZero_ellOne_isPrimary, ?_⟩
  intro p hp1 hp
  exact lp_ellOne_isPrimary p.val hp hp1

theorem corollary_3_27 : Corollary_3_27 𝕜 := cZero_infinity_isPrimary

end PFP
