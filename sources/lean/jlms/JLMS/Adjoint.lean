import JLMS.EssentialNorm
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-!
# Banach adjoints and Hahn–Banach

The norming functional is the existing real/complex Hahn–Banach theorem in
mathlib. The adjoint is the linear Banach adjoint, not a Hilbert-space adjoint.
These are the identities used in Section 7 of the paper.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

@[simp] theorem banachAdjoint_id :
    banachAdjoint (ContinuousLinearMap.id 𝕜 E) =
      ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜) := by
  ext φ x
  rfl

@[simp] theorem banachAdjoint_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    banachAdjoint (S.comp T) = (banachAdjoint T).comp (banachAdjoint S) := by
  ext φ x
  rfl

@[simp] theorem banachAdjoint_sub (S T : E →L[𝕜] F) :
    banachAdjoint (S - T) = banachAdjoint S - banachAdjoint T := by
  ext φ x
  simp [banachAdjoint_apply]

@[simp] theorem banachAdjoint_smul (a : 𝕜) (T : E →L[𝕜] F) :
    banachAdjoint (a • T) = a • banachAdjoint T := by
  ext φ x
  simp [banachAdjoint_apply]

/-- Hahn–Banach gives equality, not just the elementary upper bound. -/
@[simp] theorem norm_banachAdjoint (T : E →L[𝕜] F) : ‖banachAdjoint T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro φ
    change ‖φ.comp T‖ ≤ ‖T‖ * ‖φ‖
    simpa [mul_comm] using ContinuousLinearMap.opNorm_comp_le φ T
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (banachAdjoint T))
    intro x
    obtain ⟨φ, hφ, hx⟩ := exists_dual_vector'' 𝕜 (T x)
    calc
      ‖T x‖ = ‖φ (T x)‖ := by rw [hx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      _ = ‖banachAdjoint T φ x‖ := rfl
      _ ≤ ‖banachAdjoint T φ‖ * ‖x‖ := (banachAdjoint T φ).le_opNorm x
      _ ≤ (‖banachAdjoint T‖ * ‖φ‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right ((banachAdjoint T).le_opNorm φ) (norm_nonneg x)
      _ ≤ ‖banachAdjoint T‖ * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left hφ (norm_nonneg (banachAdjoint T)))
          (norm_nonneg x)

theorem dualEssentialNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ dualEssentialNorm T :=
  essentialNorm_nonneg _

theorem dualEssentialNorm_le_norm (T : E →L[𝕜] F) : dualEssentialNorm T ≤ ‖T‖ := by
  simpa [dualEssentialNorm] using essentialNorm_le_norm (banachAdjoint T)

@[simp] theorem dualEssentialNorm_smul (a : 𝕜) (T : E →L[𝕜] F) :
    dualEssentialNorm (a • T) = ‖a‖ * dualEssentialNorm T := by
  simp [dualEssentialNorm]

end JLMS
