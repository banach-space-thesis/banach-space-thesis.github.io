import ThesisCommon.Analysis.WeakEssentialNormProperties
import ThesisCommon.Analysis.WeakCompactClosed

/-! The actual quotient norm on the weak Calkin algebra. Norm closedness of
the weakly compact operators makes the quotient seminorm definite. -/

noncomputable section
set_option synthInstance.maxSize 1024

namespace ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- This instance equips the ordinary operator quotient with its genuine norm. -/
instance weaklyCompactSubmodule_isClosed [CompleteSpace F] :
    IsClosed (weaklyCompactSubmodule 𝕜 E F : Set (E →L[𝕜] F)) :=
  isClosed_weaklyCompactSubmodule

/-- For a Banach range, zero distance is equivalent to weak compactness. -/
theorem weakEssentialNorm_eq_zero_iff [CompleteSpace F] (T : E →L[𝕜] F) :
    weakEssentialNorm T = 0 ↔ IsWeaklyCompactOperator T := by
  letI : IsClosed ((weaklyCompactSubmodule 𝕜 E F).toAddSubgroup : Set (E →L[𝕜] F)) :=
    isClosed_weaklyCompactSubmodule (𝕜 := 𝕜) (E := E) (F := F)
  rw [weakEssentialNorm_eq_quotient_norm]
  exact QuotientAddGroup.norm_mk_eq_zero
    (S := (weaklyCompactSubmodule 𝕜 E F).toAddSubgroup) (m := T)

/-- The weak Calkin norm is the actual quotient norm, with its existing topology. -/
def weakCalkinNorm (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    WeakCalkin 𝕜 E → ℝ := norm

@[simp] theorem weakCalkinNorm_eq_norm (x : WeakCalkin 𝕜 E) :
    weakCalkinNorm 𝕜 E x = ‖x‖ := rfl

/-- Pulling the actual quotient norm back to operators gives the weak essential norm. -/
@[simp] theorem norm_weakCalkinMk (T : E →L[𝕜] E) :
    ‖weakCalkinMk 𝕜 E T‖ = weakEssentialNorm T :=
  (weakEssentialNorm_eq_quotient_norm T).symm

@[simp] theorem weakCalkinNorm_mk (T : E →L[𝕜] E) :
    weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T) = weakEssentialNorm T :=
  norm_weakCalkinMk T

/-- The canonical quotient norm satisfies the paper's algebra-norm interface. -/
theorem weakCalkinNorm_isAlgebraNorm [CompleteSpace E] :
    IsWeakCalkinAlgebraNorm 𝕜 E (weakCalkinNorm 𝕜 E) := by
  refine ⟨fun x => norm_nonneg x, ?_,
    fun x y => norm_add_le x y, ?_, ?_⟩
  · intro x
    refine Submodule.Quotient.induction_on _ x fun T => ?_
    change weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T) = 0 ↔
      (Submodule.Quotient.mk T : WeakCalkin 𝕜 E) = 0
    rw [weakCalkinNorm_mk, weakEssentialNorm_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    rfl
  · intro a x
    refine Submodule.Quotient.induction_on _ x fun T => ?_
    change weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E (a • T)) =
      ‖a‖ * weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T)
    simpa only [weakCalkinNorm_mk] using weakEssentialNorm_smul a T
  · intro S T
    simpa only [weakCalkinNorm_mk] using weakEssentialNorm_comp_le S T

/-- Existence here is constructive from the usual quotient norm; no minimality
or uniqueness hypothesis on algebra norms is used. -/
theorem exists_weakCalkinAlgebraNorm [CompleteSpace E] :
    ∃ n : WeakCalkin 𝕜 E → ℝ, IsWeakCalkinAlgebraNorm 𝕜 E n ∧
      ∀ T : E →L[𝕜] E, n (weakCalkinMk 𝕜 E T) = weakEssentialNorm T :=
  ⟨weakCalkinNorm 𝕜 E, weakCalkinNorm_isAlgebraNorm, weakCalkinNorm_mk⟩

/-- The canonical quotient projection as an actual continuous linear map. -/
def weakCalkinMkCLM (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    (E →L[𝕜] E) →L[𝕜] WeakCalkin 𝕜 E where
  toLinearMap := (weaklyCompactSubmodule 𝕜 E E).mkQ
  cont := continuous_quot_mk

@[simp] theorem weakCalkinMkCLM_apply (T : E →L[𝕜] E) :
    weakCalkinMkCLM 𝕜 E T = weakCalkinMk 𝕜 E T := rfl

theorem weakCalkinMkCLM_norm_apply_le (T : E →L[𝕜] E) :
    ‖weakCalkinMkCLM 𝕜 E T‖ ≤ ‖T‖ := by
  simpa only [weakCalkinMkCLM_apply, norm_weakCalkinMk] using
    weakEssentialNorm_le_norm T

/-- The canonical norm makes the quotient a complete space when the original
space is Banach. -/
theorem weakCalkin_completeSpace [CompleteSpace E] : CompleteSpace (WeakCalkin 𝕜 E) :=
  inferInstance

end ThesisCommon
