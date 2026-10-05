import ThesisCommon.Analysis.GowersMaureySeminormTailTests

/-! A genuine lower bound on a subspace containing an infinite nonzero
block sequence forces a positive block operator seminorm. The test vectors
are the proved small-interval vectors in arbitrary tails of that sequence. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem half_lower_bound_le_spaceOperatorSeminorm (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (Y : Submodule ℝ (C00 𝕜))
    (u : ℕ → C00 𝕜) (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hne : ∀ i, u i ≠ 0) (c : ℝ)
    (hb : ∀ x ∈ Y, c * implicitNorm D x ≤ ‖T (denseEmbedding D x)‖) :
    c/2 ≤ spaceOperatorSeminorm D T := by
  apply le_spaceOperatorSeminorm_of_tail_tests D T (c/2)
  intro n _ B
  obtain ⟨x, hxY, hxB, hxnorm, hxsmall⟩ := exists_small_interval_vector_after D
    Y u hu hY hne B n (ε := 1) zero_lt_one
  refine ⟨x, hxB, hxsmall, ?_⟩
  have hh := hb x hxY
  rw [hxnorm] at hh
  norm_num only [one_add_one_eq_two] at hh
  simpa only [div_eq_mul_inv, one_mul] using hh

theorem no_block_lower_bound_of_spaceOperatorSeminorm_zero (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (hT : spaceOperatorSeminorm D T = 0)
    (Y : Submodule ℝ (C00 𝕜)) (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hne : ∀ i, u i ≠ 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Y, c * implicitNorm D x ≤ ‖T (denseEmbedding D x)‖ := by
  rintro ⟨c, hc, hb⟩
  have hh := half_lower_bound_le_spaceOperatorSeminorm D T Y u hu hY hne c hb
  rw [hT] at hh
  linarith

end ThesisCommon.GowersMaurey
