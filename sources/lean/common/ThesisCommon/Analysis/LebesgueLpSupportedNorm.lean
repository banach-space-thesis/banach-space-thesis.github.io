import ThesisCommon.Analysis.LebesgueLpRestrictions

/-! Restriction preserves the norm of an Lp vector supported on the
restricted measurable set. The support assertion is an a.e. statement. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

theorem lebesgueLpExtend_restrict_of_supported (s : Set α) (hs : MeasurableSet s)
    (f : Lp E p μ) (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    lebesgueLpExtend (𝕜 := 𝕜) s hs (lebesgueLpRestrict (𝕜 := 𝕜) s f) = f := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hs).mp (lebesgueLpRestrict_coe (𝕜 := 𝕜) s f)
  filter_upwards [lebesgueLpExtend_coe (𝕜 := 𝕜) s hs (lebesgueLpRestrict (𝕜 := 𝕜) s f),
    hr, hf] with x he hr hf
  rw [he]
  by_cases hx : x ∈ s
  · simpa [hx] using hr hx
  · simp [hx, hf hx]

theorem lebesgueLpRestrict_norm_of_supported (s : Set α) (hs : MeasurableSet s)
    (f : Lp E p μ) (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    ‖lebesgueLpRestrict (𝕜 := 𝕜) s f‖ = ‖f‖ := by
  rw [← (lebesgueLpExtend (𝕜 := 𝕜) s hs).norm_map,
    lebesgueLpExtend_restrict_of_supported s hs f hf]

end ThesisCommon
