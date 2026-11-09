import SurveyStatements.P5ScalarCompression

/-! The genuine quantitative composition step in the source's scalar
compression proof. The two analytic reduction premises are explicit and must
be established separately. No existence assertion for a multiplier is assumed
by the main theorem through this file. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P5

variable {𝕜 X : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Compressing a compression is the same as composing the exterior maps. -/
theorem compression_composition (T A₀ B₀ A₁ B₁ : X →L[𝕜] X) :
    (((A₁.comp A₀).comp T).comp (B₀.comp B₁)) =
      (A₁.comp ((A₀.comp T).comp B₀)).comp B₁ := by
  ext x
  rfl

theorem compression_composition_retraction (A₀ B₀ A₁ B₁ : X →L[𝕜] X)
    (h₀ : A₀.comp B₀ = ContinuousLinearMap.id 𝕜 X)
    (h₁ : A₁.comp B₁ = ContinuousLinearMap.id 𝕜 X) :
    (A₁.comp A₀).comp (B₀.comp B₁) = ContinuousLinearMap.id 𝕜 X := by
  apply ContinuousLinearMap.ext
  intro x
  have h₀x := congrArg (fun L : X →L[𝕜] X => L (B₁ x)) h₀
  have h₁x := congrArg (fun L : X →L[𝕜] X => L x) h₁
  change A₁ (A₀ (B₀ (B₁ x))) = x
  change A₀ (B₀ (B₁ x)) = B₁ x at h₀x
  change A₁ (B₁ x) = x at h₁x
  rw [h₀x, h₁x]

theorem compression_composition_norm_le (A₀ B₀ A₁ B₁ : X →L[𝕜] X) :
    ‖A₁.comp A₀‖ * ‖B₀.comp B₁‖ ≤
      (‖A₀‖ * ‖B₀‖) * (‖A₁‖ * ‖B₁‖) := by
  calc
    _ ≤ (‖A₁‖ * ‖A₀‖) * (‖B₀‖ * ‖B₁‖) :=
      mul_le_mul (A₁.opNorm_comp_le A₀) (B₀.opNorm_comp_le B₁)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem compression_composition_error_le (T M A₀ B₀ A₁ B₁ : X →L[𝕜] X)
    (c : 𝕜) :
    ‖((A₁.comp A₀).comp T).comp (B₀.comp B₁) - c • ContinuousLinearMap.id 𝕜 X‖ ≤
      (‖A₁‖ * ‖B₁‖) * ‖(A₀.comp T).comp B₀ - M‖ +
        ‖(A₁.comp M).comp B₁ - c • ContinuousLinearMap.id 𝕜 X‖ := by
  have heq : ((A₁.comp A₀).comp T).comp (B₀.comp B₁) - c • ContinuousLinearMap.id 𝕜 X =
      (A₁.comp ((A₀.comp T).comp B₀ - M)).comp B₁ +
        ((A₁.comp M).comp B₁ - c • ContinuousLinearMap.id 𝕜 X) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_sub]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  gcongr
  calc
    _ ≤ (‖A₁‖ * ‖(A₀.comp T).comp B₀ - M‖) * ‖B₁‖ :=
      ((A₁.comp _).opNorm_comp_le B₁).trans
        (mul_le_mul_of_nonneg_right (A₁.opNorm_comp_le _) (norm_nonneg _))
    _ = _ := by ring

/-- The paper's two reduction steps imply scalar compression. `D` is the
specified class of intermediate operators (the product Haar multipliers in
the application). Both statements remain visible premises of this lemma. -/
theorem scalarCompression_of_two_stage_reduction
    (D : (X →L[𝕜] X) → Prop)
    (hreduce : ∀ T : X →L[𝕜] X, ∀ δ : ℝ, 0 < δ →
      ∃ A₀ B₀ M : X →L[𝕜] X,
        A₀.comp B₀ = ContinuousLinearMap.id 𝕜 X ∧
        ‖A₀‖ ≤ 1 ∧ ‖B₀‖ ≤ 1 ∧ D M ∧ ‖(A₀.comp T).comp B₀ - M‖ < δ)
    (hscalar : ∀ M : X →L[𝕜] X, D M → ∀ δ : ℝ, 0 < δ →
      ∃ A₁ B₁ : X →L[𝕜] X, ∃ c : 𝕜,
        A₁.comp B₁ = ContinuousLinearMap.id 𝕜 X ∧
        ‖A₁‖ * ‖B₁‖ ≤ 1 + δ ∧
        ‖(A₁.comp M).comp B₁ - c • ContinuousLinearMap.id 𝕜 X‖ < δ) :
    HasScalarCompression 𝕜 X := by
  intro T ε hε
  let δ : ℝ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδsmall : δ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨A₀, B₀, M, h₀, hA₀, hB₀, hM, herror₀⟩ := hreduce T δ hδ
  obtain ⟨A₁, B₁, c, h₁, hnorm₁, herror₁⟩ := hscalar M hM δ hδ
  refine ⟨A₁.comp A₀, B₀.comp B₁, c,
    compression_composition_retraction A₀ B₀ A₁ B₁ h₀ h₁, ?_, ?_⟩
  · have hnorm₀ : ‖A₀‖ * ‖B₀‖ ≤ 1 :=
      (mul_le_mul hA₀ hB₀ (norm_nonneg _) zero_le_one).trans (by norm_num)
    calc
      _ ≤ (‖A₀‖ * ‖B₀‖) * (‖A₁‖ * ‖B₁‖) :=
        compression_composition_norm_le A₀ B₀ A₁ B₁
      _ ≤ 1 * (1 + δ) :=
        mul_le_mul hnorm₀ hnorm₁ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
      _ ≤ 1 + ε := by linarith
  · have herror : (‖A₁‖ * ‖B₁‖) * ‖(A₀.comp T).comp B₀ - M‖ ≤ (1 + δ) * δ :=
      mul_le_mul hnorm₁ herror₀.le (norm_nonneg _) (by linarith)
    exact (compression_composition_error_le T M A₀ B₀ A₁ B₁ c).trans_lt
      (by nlinarith)

end SurveyStatements.P5
