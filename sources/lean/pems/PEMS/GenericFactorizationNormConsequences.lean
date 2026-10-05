import PEMS.GenericFactorizationMinimality

/-! The unrestricted minimality criterion for the two actual weak Calkin
algebra norms used in the paper. -/
noncomputable section
open ThesisCommon
namespace PEMS
variable {𝕜 E Z : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

theorem minimal_weakEssentialNorm_of_generic_factorization
    (hZ : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (I Q : ℕ → Z →L[𝕜] Z)
    (hd : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 Z)
    (ho : ∀ n m, n ≠ m → (Q n).comp (I m) = 0)
    (hfactor : ∀ T : E →L[𝕜] E, weakEssentialNorm T = factorizationSup Z T) :
    IsMinimalWeakCalkinNorm 𝕜 E weakEssentialNorm := by
  have h := minimalWeakCalkinNorm_of_generic_factorization hZ I Q hd ho
    (weakCalkinNorm 𝕜 E) weakCalkinNorm_isAlgebraNorm
    (fun T => by simpa only [weakCalkinNorm_mk] using hfactor T)
  simpa only [weakCalkinNorm_mk] using h

theorem minimal_dualWeakEssentialNorm_of_generic_factorization
    (hZ : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (I Q : ℕ → Z →L[𝕜] Z)
    (hd : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 Z)
    (ho : ∀ n m, n ≠ m → (Q n).comp (I m) = 0)
    (hfactor : ∀ T : E →L[𝕜] E, dualWeakEssentialNorm T = factorizationSup Z T) :
    IsMinimalWeakCalkinNorm 𝕜 E dualWeakEssentialNorm := by
  have h := minimalWeakCalkinNorm_of_generic_factorization hZ I Q hd ho
    (dualWeakCalkinNorm 𝕜 E) dualWeakCalkinNorm_isAlgebraNorm
    (fun T => by simpa only [dualWeakCalkinNorm_mk, dualWeakEssentialNorm] using hfactor T)
  simpa only [dualWeakCalkinNorm_mk, dualWeakEssentialNorm] using h

end PEMS
