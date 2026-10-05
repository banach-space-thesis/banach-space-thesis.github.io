import ThesisCommon.Analysis.QuantitativePrimary

/-! The scalar 2-PFP used in all scalar diagonal dichotomies. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem scalar_factorization_of_half_le (T : 𝕜 →L[𝕜] 𝕜) (hT : 1 / 2 ≤ ‖T 1‖) :
    FactorsIdentityWith T 𝕜 2 := by
  have hpos : 0 < ‖T 1‖ := by linarith
  have hne : T 1 ≠ 0 := norm_pos_iff.mp hpos
  have hformula (x : 𝕜) : T x = x * T 1 := by
    have h := T.map_smul x (1 : 𝕜)
    simpa using h
  refine ⟨(T 1)⁻¹ • ContinuousLinearMap.id 𝕜 𝕜, ContinuousLinearMap.id 𝕜 𝕜, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change (T 1)⁻¹ * T x = x
    rw [hformula x]
    field_simp
  · simp only [norm_smul, norm_inv, ContinuousLinearMap.norm_id, mul_one]
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith

theorem scalar_hasCPFP_two : HasCPFP 𝕜 𝕜 2 := by
  intro T
  by_cases h : 1 / 2 ≤ ‖T 1‖
  · exact Or.inl (scalar_factorization_of_half_le T h)
  · right
    apply scalar_factorization_of_half_le
    have htri := norm_add_le (T 1) (1 - T 1)
    rw [add_sub_cancel, norm_one] at htri
    change 1 / 2 ≤ ‖1 - T 1‖
    linarith

end ThesisCommon
