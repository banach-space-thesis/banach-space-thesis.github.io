import ThesisCommon.Analysis.Factorization

/-! Approximate compression may act on a different Banach space. This is
the version needed for LPCK's reduction from lp(c0(C[0,1])) to lp(C[0,1]).
The conclusion keeps the target of the factorization explicit. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

theorem factorization_dichotomy_of_approximate_retracts {C : ℝ} (hC : 1 ≤ C)
    (T : X →L[𝕜] X) (Model : (Y →L[𝕜] Y) → Prop)
    (hdichotomy : ∀ D, Model D → FactorsIdentityWith D Y C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 Y - D) Y C)
    (hreduction : ∀ (ε : ℝ), 0 < ε →
      ∃ (A : X →L[𝕜] Y) (B : Y →L[𝕜] X) (D : Y →L[𝕜] Y),
        A.comp B = ContinuousLinearMap.id 𝕜 Y ∧
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ Model D ∧ ‖(A.comp T).comp B - D‖ < ε) :
    FactorsIdentityWith T Y (2*C) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - T) Y (2*C) := by
  have hpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨A, B, D, hAB, hA, hB, hD, he⟩ := hreduction (1/(4*C)) (by positivity)
  have hsmall : C * ‖(A.comp T).comp B-D‖ < 1/2 := by
    have hb := mul_lt_mul_of_pos_left he hpos
    have hc : C * (1/(4*C)) = (1/4 : ℝ) := by field_simp
    rw [hc] at hb
    linarith
  have transfer (S : X →L[𝕜] X)
      (h : FactorsIdentityWith ((A.comp S).comp B) Y (2*C)) : FactorsIdentityWith S Y (2*C) := by
    apply (h.of_compression A B).mono
    have hn : ‖A‖ * ‖B‖ ≤ 1 := by
      simpa using mul_le_mul hA hB (norm_nonneg _) zero_le_one
    simpa using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2*C)
  rcases factorization_dichotomy_perturb (hdichotomy D hD) hsmall with h | h
  · exact Or.inl (transfer T h)
  · apply Or.inr
    apply transfer (ContinuousLinearMap.id 𝕜 X-T)
    rwa [compression_complement T A B hAB]

end ThesisCommon
