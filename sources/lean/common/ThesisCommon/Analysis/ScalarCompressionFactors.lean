import ThesisCommon.Analysis.Factorization

/-! The exact endpoint factor bound for a contractive scalar compression. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem factorsIdentityWith_two_of_scalar_compression
    (T R V : X →L[𝕜] X) (c : 𝕜) (hR : ‖R‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hc : 1 / 2 ≤ ‖c‖)
    (hcomp : (R.comp T).comp V = c • ContinuousLinearMap.id 𝕜 X) :
    FactorsIdentityWith T X 2 := by
  have hcpos : 0 < ‖c‖ := by linarith
  have hcne : c ≠ 0 := norm_pos_iff.mp hcpos
  refine ⟨c⁻¹ • R, V, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    have h := DFunLike.congr_fun hcomp x
    change R (T (V x)) = c • x at h
    change c⁻¹ • R (T (V x)) = x
    rw [h, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  · have hinv : ‖c⁻¹‖ ≤ 2 := by
      rw [norm_inv, inv_eq_one_div, div_le_iff₀ hcpos]
      linarith
    rw [norm_smul]
    calc
      ‖c⁻¹‖ * ‖R‖ * ‖V‖ ≤ 2 * 1 * 1 := by
        exact mul_le_mul (mul_le_mul hinv hR (norm_nonneg R) (by norm_num)) hV
          (norm_nonneg V) (by norm_num)
      _ = 2 := by norm_num

theorem scalar_compression_factor_dichotomy
    (T R V : X →L[𝕜] X) (c : 𝕜) (hR : ‖R‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hRV : R.comp V = ContinuousLinearMap.id 𝕜 X)
    (hcomp : (R.comp T).comp V = c • ContinuousLinearMap.id 𝕜 X) :
    FactorsIdentityWith T X 2 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - T) X 2 := by
  by_cases hc : 1 / 2 ≤ ‖c‖
  · exact Or.inl (factorsIdentityWith_two_of_scalar_compression T R V c hR hV hc hcomp)
  · right
    have htri := norm_add_le c (1 - c)
    rw [add_sub_cancel, norm_one] at htri
    apply factorsIdentityWith_two_of_scalar_compression _ R V (1 - c) hR hV (by linarith)
    apply ContinuousLinearMap.ext
    intro x
    have h := DFunLike.congr_fun hcomp x
    have hr := DFunLike.congr_fun hRV x
    change R (T (V x)) = c • x at h
    change R (V x) = x at hr
    change R (V x - T (V x)) = (1 - c) • x
    rw [map_sub, hr, h, sub_smul, one_smul]

end ThesisCommon
