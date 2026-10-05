import PEMS.Definitions
import ThesisCommon.Analysis.CZeroAdjointFactorization

/-! The sharp upper inequality in the c0-fixing formula holds for arbitrary
normed operators, over either scalar field. It follows from an actual
ell-one identity factorization through the adjoint. -/
noncomputable section
set_option maxSynthPendingDepth 3
open Set
namespace PEMS
open ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem minimumModulus_cZero_nonneg (S : CZero 𝕜 →L[𝕜] F) : 0 ≤ minimumModulus S := by
  apply le_csInf
  · exact ⟨_, ⟨cZeroSingle 0 1, (scalarCZeroSchauderBasis (𝕜 := 𝕜)).norm_vector 0, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact norm_nonneg _

theorem minimumModulus_cZero_mul_norm_le (S : CZero 𝕜 →L[𝕜] F) (x : CZero 𝕜) :
    minimumModulus S * ‖x‖ ≤ ‖S x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let u : CZero 𝕜 := ((‖x‖⁻¹ : ℝ) : 𝕜) • x
  have hu : ‖u‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ hxn]
  have h : minimumModulus S ≤ ‖S u‖ :=
    csInf_le ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact norm_nonneg _⟩ ⟨u, hu, rfl⟩
  have hs : ‖S u‖ = ‖x‖⁻¹ * ‖S x‖ := by
    dsimp only [u]
    rw [map_smul, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  rw [hs] at h
  have hh := mul_le_mul_of_nonneg_right h (norm_nonneg x)
  convert hh using 1
  field_simp

theorem minimumModulus_comp_le_dualWeakEssentialNorm
    (T : E →L[𝕜] F) (V : CZero 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1) :
    minimumModulus (T.comp V) ≤ dualWeakEssentialNorm T :=
  cZero_lower_bound_le_adjoint_weakEssentialNorm T V hV
    (minimumModulus_cZero_nonneg _) (minimumModulus_cZero_mul_norm_le _)

theorem fixesCZeroSup_le_dualWeakEssentialNorm (T : E →L[𝕜] F) :
    fixesCZeroSup T ≤ dualWeakEssentialNorm T := by
  apply csSup_le
  · refine ⟨minimumModulus (T.comp (0 : CZero 𝕜 →L[𝕜] E)),
      ⟨(0 : CZero 𝕜 →L[𝕜] E), ?_, rfl⟩⟩
    exact (norm_zero : ‖(0 : CZero 𝕜 →L[𝕜] E)‖ = 0).le.trans zero_le_one
  · rintro _ ⟨V, hV, rfl⟩
    exact minimumModulus_comp_le_dualWeakEssentialNorm T V hV

end PEMS
