import ThesisCommon.Analysis.JamesAndrewFactorization

/-! Concrete James spaces have a uniform primary factorisation bound.
The operators factoring their identity are exactly those with nonzero
action on the actual one-dimensional bidual quotient. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ⊤)
  (hpl : 1 < p.val.toReal)

theorem james_factors_identity_iff_scalar_ne_zero
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    FactorsIdentity T (JamesSequenceSpace 𝕜 p) ↔ jamesOperatorScalar p hp hpl T ≠ 0 := by
  constructor
  · rintro ⟨U, V, heq⟩ hz
    have h := congrArg (jamesOperatorScalar p hp hpl) heq
    simp only [jamesOperatorScalar_comp, jamesOperatorScalar_id, hz, mul_zero, zero_mul] at h
    exact zero_ne_one h
  · intro h
    exact (james_nonzero_scalar_factors_identity p hp hpl T h).forget_bound

include hp hpl in
theorem james_factors_identity_iff_not_weaklyCompact
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    FactorsIdentity T (JamesSequenceSpace 𝕜 p) ↔ ¬ IsWeaklyCompactOperator T := by
  rw [james_factors_identity_iff_scalar_ne_zero p hp hpl,
    james_weaklyCompact_iff_scalar_eq_zero p hp hpl]

include hp hpl in
theorem jamesSequence_hasCPFP_four : HasCPFP 𝕜 (JamesSequenceSpace 𝕜 p) 4 := by
  have step (S : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
      (hs : (1 / 2 : ℝ) ≤ ‖jamesOperatorScalar p hp hpl S‖) :
      FactorsIdentityWith S (JamesSequenceSpace 𝕜 p) 4 := by
    have hpos : 0 < ‖jamesOperatorScalar p hp hpl S‖ := lt_of_lt_of_le (by norm_num) hs
    have hi : ‖jamesOperatorScalar p hp hpl S‖⁻¹ ≤ (2 : ℝ) := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      linarith
    exact (james_nonzero_scalar_factors_identity p hp hpl S (norm_pos_iff.mp hpos)).mono
      (by linarith)
  intro T
  by_cases ht : (1 / 2 : ℝ) ≤ ‖jamesOperatorScalar p hp hpl T‖
  · exact Or.inl (step T ht)
  · apply Or.inr
    apply step
    rw [jamesOperatorScalar_sub, jamesOperatorScalar_id]
    have htri : (1 : ℝ) ≤ ‖jamesOperatorScalar p hp hpl T‖ +
        ‖1 - jamesOperatorScalar p hp hpl T‖ := by
      have h := norm_add_le (jamesOperatorScalar p hp hpl T) (1 - jamesOperatorScalar p hp hpl T)
      simpa only [add_sub_cancel, norm_one] using h
    linarith

include hp hpl in
theorem jamesSequence_hasUPFP : HasUPFP 𝕜 (JamesSequenceSpace 𝕜 p) :=
  ⟨4, by norm_num, jamesSequence_hasCPFP_four p hp hpl⟩

end ThesisCommon
