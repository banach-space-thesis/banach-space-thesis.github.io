import PEMS.DeBlasiResiduum
import ThesisCommon.Analysis.ResiduumFactorizationBound

/-! Sharp infinity factorization forces equality of the actual residuum,
De Blasi measure and weak essential norm. The factorization premise is
explicit here and is discharged only in concrete geometric consumers. -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option synthInstance.maxSize 1024
open Set ThesisCommon
namespace PEMS
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem factorizationSup_infinity_le_residuumNorm (T : E →L[𝕜] F) :
    factorizationSup (EllInfinity 𝕜) T ≤ residuumNorm T := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, hfac, rfl⟩)
  · exact residuumNorm_nonneg T
  · exact factorization_constant_le_residuumNorm residuumNorm_id_scalarInfinity T U V hfac

theorem weakEssentialNorm_eq_residuumNorm_of_infinity_factorization
    (T : E →L[𝕜] F) (h : weakEssentialNorm T = factorizationSup (EllInfinity 𝕜) T) :
    weakEssentialNorm T = residuumNorm T :=
  le_antisymm (h.symm ▸ factorizationSup_infinity_le_residuumNorm T)
    (residuumNorm_le_weakEssentialNorm T)

theorem residuumNorm_eq_deBlasiOperator_of_infinity_factorization
    (T : E →L[𝕜] F) (h : weakEssentialNorm T = factorizationSup (EllInfinity 𝕜) T) :
    residuumNorm T = deBlasiOperator T := by
  apply le_antisymm (residuumNorm_le_deBlasiOperator T)
  exact (deBlasiOperator_le_weakEssentialNorm T).trans_eq
    (weakEssentialNorm_eq_residuumNorm_of_infinity_factorization T h)

end PEMS
