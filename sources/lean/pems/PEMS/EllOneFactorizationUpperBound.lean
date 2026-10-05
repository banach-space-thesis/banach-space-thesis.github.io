import PEMS.Definitions
import ThesisCommon.Analysis.WeakEssentialFactorizationBound

/-! The sharp upper bound in Theorem 1.4 holds for arbitrary normed source
and target spaces, over either real or complex scalars. The definition's
adjoined zero also handles the absence of any identity factorization. -/
noncomputable section
open Set ThesisCommon
namespace PEMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem factorizationSup_ellOne_le_weakEssentialNorm (T : E →L[𝕜] F) :
    factorizationSup (EllOne 𝕜) T ≤ weakEssentialNorm T := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, h, rfl⟩)
  · exact weakEssentialNorm_nonneg T
  · exact scalarEllOne_factorization_constant_le_weakEssentialNorm T U V h

end PEMS
