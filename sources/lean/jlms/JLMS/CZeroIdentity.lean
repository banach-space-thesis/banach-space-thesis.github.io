import JLMS.CZeroTools
import JLMS.IdentityEssentialNorm

/-!
# The c₀ and c₀* identity inputs

Coordinate vectors and evaluations give infinite linearly independent families.
Consequently both identities have essential norm one. No dual identification
with ℓ¹ is needed for this input to the upper bound in Theorem 1.7.
-/

noncomputable section

namespace JLMS

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The nth coordinate vector, in mathlib's actual C₀(ℕ) model of c₀. -/
def cZeroUnit (n : ℕ) : cZero 𝕜 :=
  clopenIndicator {n} (isClopen_discrete _) isCompact_singleton

@[simp] theorem cZeroUnit_apply (n m : ℕ) : cZeroUnit 𝕜 n m = if m = n then 1 else 0 := by
  simp [cZeroUnit]

theorem cZeroUnit_linearIndependent : LinearIndependent 𝕜 (cZeroUnit 𝕜) := by
  apply linearIndependent_iff'.mpr
  intro s a h n hn
  have he := congrArg (evaluation (𝕜 := 𝕜) n) h
  simp only [map_sum, map_smul, map_zero, evaluation_apply, cZeroUnit_apply, smul_eq_mul] at he
  simpa [hn, eq_comm] using he

theorem cZero_evaluation_linearIndependent :
    LinearIndependent 𝕜 (fun n : ℕ => evaluation (𝕜 := 𝕜) n) := by
  apply linearIndependent_iff'.mpr
  intro s a h n hn
  have he := congrArg (fun φ : cZero 𝕜 →L[𝕜] 𝕜 => φ (cZeroUnit 𝕜 n)) h
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, evaluation_apply, cZeroUnit_apply, smul_eq_mul] at he
  simpa [hn] using he

theorem cZero_not_finiteDimensional : ¬ FiniteDimensional 𝕜 (cZero 𝕜) := by
  intro h
  letI := h
  exact Module.Finite.not_linearIndependent_of_infinite _ (cZeroUnit_linearIndependent 𝕜)

theorem cZero_dual_not_finiteDimensional : ¬ FiniteDimensional 𝕜 (cZero 𝕜 →L[𝕜] 𝕜) := by
  intro h
  letI := h
  exact Module.Finite.not_linearIndependent_of_infinite _ (cZero_evaluation_linearIndependent 𝕜)

theorem essentialNorm_cZero_identity :
    essentialNorm (ContinuousLinearMap.id 𝕜 (cZero 𝕜)) = 1 :=
  essentialNorm_identity (cZero_not_finiteDimensional 𝕜)

theorem essentialNorm_cZero_dual_identity :
    essentialNorm (𝕜 := 𝕜) (E := cZero 𝕜 →L[𝕜] 𝕜) (F := cZero 𝕜 →L[𝕜] 𝕜)
      (ContinuousLinearMap.id 𝕜 (cZero 𝕜 →L[𝕜] 𝕜)) = 1 :=
  essentialNorm_identity (cZero_dual_not_finiteDimensional 𝕜)

end JLMS
