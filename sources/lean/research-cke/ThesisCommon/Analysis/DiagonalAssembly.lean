import ThesisCommon.Analysis.Factorization

/-! The common concluding argument after diagonal reduction.
This is explicitly CONDITIONAL on the analytic reduction and the dichotomy
for the chosen class of model operators. It proves neither input.
-/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Reduce T to a model D up to a small error in a contractive retract.
The condition AB = I transfers the complementary branch as well.
Source: the concluding arguments of UPFP 1.1/1.2 and LPCK Section 5. -/
theorem factorization_dichotomy_of_approximate_compressions {C : ℝ} (hC : 1 ≤ C)
    (T : X →L[𝕜] X)
    (Model : (X →L[𝕜] X) → Prop)
    (hdichotomy : ∀ D, Model D → FactorsIdentityWith D X C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - D) X C)
    (hreduction : ∀ (ε : ℝ), 0 < ε →
      ∃ A B D : X →L[𝕜] X,
        A.comp B = ContinuousLinearMap.id 𝕜 X ∧
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ Model D ∧ ‖(A.comp T).comp B - D‖ < ε) :
    FactorsIdentityWith T X (2 * C) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - T) X (2 * C) := by
  have hpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨A, B, D, hAB, hnA, hnB, hD, he⟩ :=
    hreduction (1 / (4 * C)) (by positivity)
  have hsmall : C * ‖(A.comp T).comp B - D‖ < 1 / 2 := by
    have hb := mul_lt_mul_of_pos_left he hpos
    have hc : C * (1 / (4 * C)) = (1 / 4 : ℝ) := by field_simp
    rw [hc] at hb
    linarith
  have transfer (S : X →L[𝕜] X)
      (h : FactorsIdentityWith ((A.comp S).comp B) X (2 * C)) :
      FactorsIdentityWith S X (2 * C) := by
    apply (h.of_compression A B).mono
    have hn : ‖A‖ * ‖B‖ ≤ 1 := by
      simpa using mul_le_mul hnA hnB (norm_nonneg _) zero_le_one
    simpa using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2 * C)
  rcases factorization_dichotomy_perturb (hdichotomy D hD) hsmall with h | h
  · exact Or.inl (transfer T h)
  · apply Or.inr
    apply transfer (ContinuousLinearMap.id 𝕜 X - T)
    rwa [compression_complement T A B hAB]

/-- Applying the individual-operator assembly to every operator gives C-PFP. -/
theorem hasCPFP_of_approximate_compressions {C : ℝ} (hC : 1 ≤ C)
    (Model : (X →L[𝕜] X) → Prop)
    (hdichotomy : ∀ D, Model D → FactorsIdentityWith D X C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - D) X C)
    (hreduction : ∀ (T : X →L[𝕜] X) (ε : ℝ), 0 < ε →
      ∃ A B D : X →L[𝕜] X,
        A.comp B = ContinuousLinearMap.id 𝕜 X ∧
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ Model D ∧ ‖(A.comp T).comp B - D‖ < ε) :
    HasCPFP 𝕜 X (2 * C) := by
  intro T
  exact factorization_dichotomy_of_approximate_compressions hC T Model hdichotomy (hreduction T)

end ThesisCommon
