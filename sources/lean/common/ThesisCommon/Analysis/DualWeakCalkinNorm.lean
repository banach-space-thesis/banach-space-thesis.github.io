import ThesisCommon.Analysis.WeakCalkinNorm
import ThesisCommon.Analysis.AdjointWeakEssentialNorm

/-! The adjoint weak essential norm descends to an actual algebra norm on
the weak Calkin quotient. Definiteness follows from Gantmacher duality. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
namespace ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def weakCalkinAdjointMap : WeakCalkin 𝕜 E →ₗ[𝕜] WeakCalkin 𝕜 (StrongDual 𝕜 E) :=
  (weaklyCompactSubmodule 𝕜 E E).liftQ
    ((weaklyCompactSubmodule 𝕜 (StrongDual 𝕜 E) (StrongDual 𝕜 E)).mkQ.comp
      (ContinuousLinearMap.compL 𝕜 E E 𝕜).flip.toLinearMap) (by
        intro T hT
        exact (Submodule.Quotient.mk_eq_zero _).mpr hT.banachAdjoint)

@[simp] theorem weakCalkinAdjointMap_mk (T : E →L[𝕜] E) :
    weakCalkinAdjointMap (weakCalkinMk 𝕜 E T) =
      weakCalkinMk 𝕜 (StrongDual 𝕜 E) (banachAdjoint T) := rfl

def dualWeakCalkinNorm (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : WeakCalkin 𝕜 E) : ℝ :=
  ‖weakCalkinAdjointMap (𝕜 := 𝕜) (E := E) x‖

@[simp] theorem dualWeakCalkinNorm_mk (T : E →L[𝕜] E) :
    dualWeakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T) = weakEssentialNorm (banachAdjoint T) :=
  norm_weakCalkinMk _

theorem dualWeakCalkinNorm_le_weakCalkinNorm (x : WeakCalkin 𝕜 E) :
    dualWeakCalkinNorm 𝕜 E x ≤ weakCalkinNorm 𝕜 E x := by
  refine Submodule.Quotient.induction_on _ x fun T => ?_
  change dualWeakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T) ≤
    weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T)
  rw [dualWeakCalkinNorm_mk, weakCalkinNorm_mk]
  exact weakEssentialNorm_banachAdjoint_le T

theorem dualWeakCalkinNorm_isAlgebraNorm [CompleteSpace E] :
    IsWeakCalkinAlgebraNorm 𝕜 E (dualWeakCalkinNorm 𝕜 E) := by
  refine ⟨fun x => norm_nonneg _, ?_, ?_, ?_, ?_⟩
  · intro x
    refine Submodule.Quotient.induction_on _ x fun T => ?_
    change dualWeakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T) = 0 ↔
      (Submodule.Quotient.mk T : WeakCalkin 𝕜 E) = 0
    rw [dualWeakCalkinNorm_mk, weakEssentialNorm_eq_zero_iff,
      weaklyCompact_banachAdjoint_iff, Submodule.Quotient.mk_eq_zero]
    rfl
  · intro x y
    change ‖weakCalkinAdjointMap (𝕜 := 𝕜) (E := E) (x+y)‖ ≤
      ‖weakCalkinAdjointMap (𝕜 := 𝕜) (E := E) x‖ +
      ‖weakCalkinAdjointMap (𝕜 := 𝕜) (E := E) y‖
    rw [map_add]
    exact norm_add_le _ _
  · intro a x
    refine Submodule.Quotient.induction_on _ x fun T => ?_
    change dualWeakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E (a • T)) =
      ‖a‖ * dualWeakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T)
    rw [dualWeakCalkinNorm_mk, dualWeakCalkinNorm_mk, banachAdjoint_smul,
      weakEssentialNorm_smul]
  · intro S T
    simp only [dualWeakCalkinNorm_mk, banachAdjoint_comp]
    exact (weakEssentialNorm_comp_le _ _).trans_eq (mul_comm _ _)

theorem exists_dualWeakCalkinAlgebraNorm [CompleteSpace E] :
    ∃ n : WeakCalkin 𝕜 E → ℝ, IsWeakCalkinAlgebraNorm 𝕜 E n ∧
      ∀ T : E →L[𝕜] E, n (weakCalkinMk 𝕜 E T) = weakEssentialNorm (banachAdjoint T) :=
  ⟨dualWeakCalkinNorm 𝕜 E, dualWeakCalkinNorm_isAlgebraNorm, dualWeakCalkinNorm_mk⟩

end ThesisCommon
