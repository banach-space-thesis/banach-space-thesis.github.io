import ThesisCommon.Analysis.SharpFactorization

/-! Sharp perturbation after compressions with a bounded norm product.
No separate contractivity of the compression maps is assumed. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem hasCPlusPFP_of_bounded_approximate_compressions
    {C D : ℝ} (hC : 0 < C) (hD : 0 < D) (Model : (X →L[𝕜] X) → Prop)
    (hdichotomy : ∀ M, Model M → FactorsIdentityWith M X C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - M) X C)
    (hreduction : ∀ (T : X →L[𝕜] X) (η : ℝ), 0 < η →
      ∃ A B M : X →L[𝕜] X,
        A.comp B = ContinuousLinearMap.id 𝕜 X ∧
        ‖A‖ * ‖B‖ ≤ D ∧ Model M ∧ ‖(A.comp T).comp B - M‖ < η) :
    HasCPlusPFP 𝕜 X (C * D) := by
  intro ε hε T
  let r := ε / (C * D + ε)
  have hden : 0 < C * D + ε := add_pos (mul_pos hC hD) hε
  have hrpos : 0 < r := div_pos hε hden
  have hr : r < 1 := (div_lt_one hden).mpr (by nlinarith [mul_pos hC hD])
  have hfrac : (C * D + ε) * (1 - r) = C * D := by
    dsimp [r]
    field_simp [hden.ne']
    ring
  have hconst : (C / (1 - r)) * D = C * D + ε := by
    rw [div_mul_eq_mul_div]
    exact (div_eq_iff (sub_pos.mpr hr).ne').mpr hfrac.symm
  have hq : 0 ≤ C / (1 - r) := (div_pos hC (sub_pos.mpr hr)).le
  obtain ⟨A, B, M, hAB, hnorm, hM, he⟩ := hreduction T (r / C) (div_pos hrpos hC)
  have hsmall : C * ‖(A.comp T).comp B - M‖ ≤ r := by
    have hmul := mul_lt_mul_of_pos_left he hC
    have heq : C * (r / C) = r := by field_simp
    rw [heq] at hmul
    exact hmul.le
  have transfer (S : X →L[𝕜] X)
      (h : FactorsIdentityWith ((A.comp S).comp B) X (C / (1 - r))) :
      FactorsIdentityWith S X (C * D + ε) := by
    apply (h.of_compression A B).mono
    exact (mul_le_mul_of_nonneg_left hnorm hq).trans_eq hconst
  rcases hdichotomy M hM with h | h
  · exact Or.inl (transfer T (h.perturb_fraction hr hsmall))
  · right
    apply transfer (ContinuousLinearMap.id 𝕜 X - T)
    rw [compression_complement T A B hAB]
    apply h.perturb_fraction hr
    simpa only [sub_sub_sub_cancel_left, norm_sub_rev] using hsmall

end ThesisCommon
