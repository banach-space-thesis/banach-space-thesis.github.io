import ThesisCommon.Analysis.DiagonalAssembly
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! The concluding diagonal argument when the space being compressed is
isomorphic to the factor space. The distortion is a fixed uniform constant. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Contractive approximate retractions from Y onto X, together with a
model dichotomy on X and an actual isomorphism X ≃ Y, imply UPFP of Y. -/
theorem hasUPFP_of_approximate_retractions {C : ℝ} (hC : 1 ≤ C)
    (e : X ≃L[𝕜] Y) (Model : (X →L[𝕜] X) → Prop)
    (hdichotomy : ∀ D, Model D → FactorsIdentityWith D X C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - D) X C)
    (hreduction : ∀ (T : Y →L[𝕜] Y) (ε : ℝ), 0 < ε →
      ∃ (A : Y →L[𝕜] X) (B : X →L[𝕜] Y) (D : X →L[𝕜] X),
        A.comp B = ContinuousLinearMap.id 𝕜 X ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
          Model D ∧ ‖(A.comp T).comp B - D‖ < ε) : HasUPFP 𝕜 Y := by
  let d := ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖
  have hd : 0 ≤ d := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨max 1 (2 * C * d), le_max_left _ _, ?_⟩
  intro T
  have hpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨A, B, D, hAB, hnA, hnB, hD, he⟩ :=
    hreduction T (1 / (4 * C)) (by positivity)
  have hsmall : C * ‖(A.comp T).comp B - D‖ < 1 / 2 := by
    have hb := mul_lt_mul_of_pos_left he hpos
    have hc : C * (1 / (4 * C)) = (1 / 4 : ℝ) := by field_simp
    rw [hc] at hb
    linarith
  have transfer (S : Y →L[𝕜] Y)
      (h : FactorsIdentityWith ((A.comp S).comp B) X (2 * C)) :
      FactorsIdentityWith S Y (max 1 (2 * C * d)) := by
    have h' := (h.of_compression A B).target_equiv e
    apply h'.mono
    have hn : ‖A‖ * ‖B‖ ≤ 1 := by
      simpa using mul_le_mul hnA hnB (norm_nonneg _) zero_le_one
    apply le_trans _ (le_max_right _ _)
    change (2 * C * (‖A‖ * ‖B‖)) * d ≤ 2 * C * d
    exact mul_le_mul_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2 * C)) hd
  rcases factorization_dichotomy_perturb (hdichotomy D hD) hsmall with h | h
  · exact Or.inl (transfer T h)
  · apply Or.inr
    apply transfer (ContinuousLinearMap.id 𝕜 Y - T)
    rwa [compression_complement T A B hAB]

end ThesisCommon
