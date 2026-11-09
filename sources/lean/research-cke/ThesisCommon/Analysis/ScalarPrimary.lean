import ThesisCommon.Analysis.Primary

/-! The scalar field has 2-PFP. This is the quantitative base case for
finite compact spaces and for the scalar sequence-space endpoints. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem scalar_operator_apply (T : 𝕜 →L[𝕜] 𝕜) (z : 𝕜) : T z = T 1 * z := by
  calc
    T z = T (z • (1 : 𝕜)) := by simp
    _ = z • T 1 := T.map_smul z 1
    _ = T 1 * z := mul_comm _ _

theorem scalar_factorsIdentityWith_of_half_le (T : 𝕜 →L[𝕜] 𝕜)
    (hT : (1/2 : ℝ) ≤ ‖T 1‖) : FactorsIdentityWith T 𝕜 2 := by
  have hn : T 1 ≠ 0 := norm_pos_iff.1 (by linarith)
  let U : 𝕜 →L[𝕜] 𝕜 := (T 1)⁻¹ • ContinuousLinearMap.id 𝕜 𝕜
  refine ⟨U, ContinuousLinearMap.id 𝕜 𝕜, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro z
    change (T 1)⁻¹ * T z = z
    rw [scalar_operator_apply T z, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · change ‖(T 1)⁻¹ • ContinuousLinearMap.id 𝕜 𝕜‖ * ‖ContinuousLinearMap.id 𝕜 𝕜‖ ≤ 2
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, mul_one, norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.2 hn) (by norm_num : (0 : ℝ) < 2)).2 (by simpa using hT)

theorem scalar_hasCPFP : HasCPFP 𝕜 𝕜 2 := by
  intro T
  by_cases hT : (1/2 : ℝ) ≤ ‖T 1‖
  · exact Or.inl (scalar_factorsIdentityWith_of_half_le T hT)
  · apply Or.inr
    apply scalar_factorsIdentityWith_of_half_le
    have hn := norm_add_le (T 1) (1 - T 1)
    have he : T 1 + (1 - T 1) = (1 : 𝕜) := by ring
    rw [he, norm_one] at hn
    change (1/2 : ℝ) ≤ ‖1 - T 1‖
    linarith

theorem scalar_hasUPFP : HasUPFP 𝕜 𝕜 := ⟨2, by norm_num, scalar_hasCPFP⟩

end ThesisCommon
