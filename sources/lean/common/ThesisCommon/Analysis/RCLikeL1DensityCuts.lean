import ThesisCommon.Analysis.L1DensityEquivRCLike
import ThesisCommon.Analysis.LebesgueLpRestrictions
import ThesisCommon.LpCut

/-! Positive-density L1 isometries and actual restriction/zero extension
commute with measurable indicator multiplication for both scalars. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
variable {g : X → ℝ≥0}

theorem lOneWithDensityEquiv_rclike_cut (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) (A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 (μ.withDensity (fun x => (g x : ENNReal)))) :
    lOneWithDensityEquiv_rclike hg hpos (lpCut A hA f) =
      lpCut A hA (lOneWithDensityEquiv_rclike hg hpos f) := by
  apply Lp.ext
  filter_upwards [withDensitySMulLI_coe_rclike hg (lpCut A hA f),
    withDensitySMulLI_coe_rclike hg f,
    lpCut_coe A hA (lOneWithDensityEquiv_rclike hg hpos f),
    (ae_withDensity_coe_iff_of_pos hg hpos).mp (lpCut_coe A hA f)] with x hl hf hr hc
  change lOneWithDensityEquiv_rclike hg hpos (lpCut A hA f) x = _
  change lOneWithDensityEquiv_rclike hg hpos (lpCut A hA f) x = (g x : ℝ) • lpCut A hA f x at hl
  change lOneWithDensityEquiv_rclike hg hpos f x = (g x : ℝ) • f x at hf
  rw [hl, hc, hr]
  by_cases hx : x ∈ A <;> simp [hx, hf]

theorem lOneWithDensityEquiv_rclike_symm_cut (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) (A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 μ) :
    (lOneWithDensityEquiv_rclike hg hpos).symm (lpCut A hA f) =
      lpCut A hA ((lOneWithDensityEquiv_rclike hg hpos).symm f) := by
  apply (lOneWithDensityEquiv_rclike hg hpos).injective
  rw [LinearIsometryEquiv.apply_symm_apply, lOneWithDensityEquiv_rclike_cut,
    LinearIsometryEquiv.apply_symm_apply]

theorem lebesgueL1Restrict_cut_rclike (Ω A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 μ) :
    lebesgueLpRestrict (𝕜 := 𝕜) Ω (lpCut A hA f) =
      lpCut A hA (lebesgueLpRestrict (𝕜 := 𝕜) Ω f) := by
  apply Lp.ext
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) Ω (lpCut A hA f),
    lebesgueLpRestrict_coe (𝕜 := 𝕜) Ω f,
    ae_restrict_of_ae (lpCut_coe A hA f),
    lpCut_coe A hA (lebesgueLpRestrict (𝕜 := 𝕜) Ω f)] with x hr hf hc hc'
  rw [hr, hc, hc']
  by_cases hx : x ∈ A <;> simp [hx, hf]

theorem lebesgueL1Extend_cut_rclike (Ω : Set X) (hΩ : MeasurableSet Ω)
    (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 1 (μ.restrict Ω)) :
    lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ (lpCut A hA f) =
      lpCut A hA (lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ f) := by
  apply Lp.ext
  filter_upwards [lebesgueLpExtend_coe (𝕜 := 𝕜) Ω hΩ (lpCut A hA f),
    lebesgueLpExtend_coe (𝕜 := 𝕜) Ω hΩ f,
    (ae_restrict_iff' hΩ).mp (lpCut_coe A hA f),
    lpCut_coe A hA (lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ f)] with x he hf hc hc'
  rw [he, hc']
  by_cases hxΩ : x ∈ Ω
  · rw [indicator_of_mem hxΩ, hc hxΩ]
    by_cases hxA : x ∈ A <;> simp [hxA, hf, hxΩ]
  · by_cases hxA : x ∈ A <;> simp [hxA, hxΩ, hf]

end ThesisCommon
