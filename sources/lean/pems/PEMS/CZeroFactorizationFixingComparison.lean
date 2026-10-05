import PEMS.CZeroFixingUpperBound
import PEMS.FactorizationSupContractions
import ThesisCommon.Analysis.CZeroInfinityEmbedding

/-! Every actual identity factorization through a space containing c₀
is bounded by the c₀-fixing supremum. This gives the common upper bound
for both factorization clauses of Theorem 1.5. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open Set ThesisCommon
open scoped ENNReal
namespace PEMS
variable {𝕜 E F Z : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [Nontrivial Z]

theorem factorization_constant_le_fixesCZeroSup (i : CZero 𝕜 →ₗᵢ[𝕜] Z)
    (T : E →L[𝕜] F) (U : F →L[𝕜] Z) (W : Z →L[𝕜] E)
    (hfact : U.comp (T.comp W) = ContinuousLinearMap.id 𝕜 Z) :
    ‖U‖⁻¹*‖W‖⁻¹ ≤ fixesCZeroSup T := by
  letI : NormedAddCommGroup (F →L[𝕜] Z) :=
    ContinuousLinearMap.toNormedAddCommGroup (E := F) (F := Z) (σ₁₂ := RingHom.id 𝕜)
  letI : NormedAddCommGroup (Z →L[𝕜] E) :=
    ContinuousLinearMap.toNormedAddCommGroup (E := Z) (F := E) (σ₁₂ := RingHom.id 𝕜)
  have hid : (ContinuousLinearMap.id 𝕜 Z) ≠ 0 := by
    intro h
    have hn := congrArg norm h
    simp at hn
  have hUne : U ≠ 0 := by intro h; apply hid; rw [← hfact, h]; ext x; simp
  have hWne : W ≠ 0 := by intro h; apply hid; rw [← hfact, h]; ext x; simp
  have hUn : 0 < ‖U‖ := norm_pos_iff.mpr hUne
  have hWn : 0 < ‖W‖ := norm_pos_iff.mpr hWne
  let L : CZero 𝕜 →L[𝕜] E := ((‖W‖⁻¹ : ℝ) : 𝕜) • W.comp i.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖((‖W‖⁻¹ : ℝ) : 𝕜) • W (i x)‖ ≤ 1*‖x‖
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hWn), one_mul]
    have h := mul_le_mul_of_nonneg_left (W.le_opNorm (i x)) (inv_nonneg.mpr hWn.le)
    rw [i.norm_map, ← mul_assoc, inv_mul_cancel₀ hWn.ne', one_mul] at h
    exact h
  have hmin : ‖U‖⁻¹*‖W‖⁻¹ ≤ minimumModulus (T.comp L) := by
    apply le_csInf
    · exact ⟨_, ⟨cZeroSingle 0 1, (scalarCZeroSchauderBasis (𝕜 := 𝕜)).norm_vector 0, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      have heq : U (T (W (i x))) = i x := DFunLike.congr_fun hfact (i x)
      have hu := U.le_opNorm (T (W (i x)))
      rw [heq, i.norm_map, hx] at hu
      have hh : ‖U‖⁻¹ ≤ ‖T (W (i x))‖ := by
        rw [← one_div, div_le_iff₀ hUn]
        simpa only [mul_comm] using hu
      have h := mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hWn.le)
      change _ ≤ ‖T (((‖W‖⁻¹ : ℝ) : 𝕜) • W (i x))‖
      rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hWn)]
      simpa only [mul_comm] using h
  apply hmin.trans
  apply le_csSup
  · refine ⟨dualWeakEssentialNorm T, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    exact minimumModulus_comp_le_dualWeakEssentialNorm T A hA
  · exact ⟨L, hL, rfl⟩

theorem factorizationSup_le_fixesCZeroSup_of_isometry
    (i : CZero 𝕜 →ₗᵢ[𝕜] Z) (T : E →L[𝕜] F) :
    factorizationSup Z T ≤ fixesCZeroSup T := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, W, h, rfl⟩)
  · apply (minimumModulus_cZero_nonneg (T.comp (0 : CZero 𝕜 →L[𝕜] E))).trans
    apply le_csSup
    · refine ⟨dualWeakEssentialNorm T, ?_⟩
      rintro _ ⟨A, hA, rfl⟩
      exact minimumModulus_comp_le_dualWeakEssentialNorm T A hA
    · refine ⟨0, ?_, rfl⟩
      simp
  · exact factorization_constant_le_fixesCZeroSup i T U W h

theorem factorizationSup_cZero_le_fixesCZeroSup (T : E →L[𝕜] F) :
    factorizationSup (CZero 𝕜) T ≤ fixesCZeroSup T := by
  letI : Nontrivial (CZero 𝕜) := ⟨⟨cZeroSingle 0 1, 0, by
    intro h
    have hh := congrArg (fun x : CZero 𝕜 => x 0) h
    simp at hh⟩⟩
  exact factorizationSup_le_fixesCZeroSup_of_isometry (LinearIsometry.id) T

theorem factorizationSup_infinity_le_fixesCZeroSup (T : E →L[𝕜] F) :
    factorizationSup (EllInfinity 𝕜) T ≤ fixesCZeroSup T := by
  letI : Nontrivial (EllInfinity 𝕜) := ⟨⟨lp.single ∞ 0 (1 : 𝕜), 0, by
    intro h
    have hh := congrArg (fun x : EllInfinity 𝕜 => x 0) h
    simp at hh⟩⟩
  exact factorizationSup_le_fixesCZeroSup_of_isometry cZeroToInfinityIsometry T

end PEMS
