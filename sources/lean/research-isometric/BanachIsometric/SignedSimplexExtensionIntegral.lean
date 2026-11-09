import BanachIsometric.SignedSimplexCount

/-! A compatible extension may be used in the simplex integral. This makes it
possible to choose a single operator-valued extension before evaluating any
vector, and to use positive rescalings of a fixed reference extension. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Filter MeasureTheory
open scoped Topology NNReal

theorem ae_restrict_signedSimplexDomain_mem_interior (n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ.restrict (signedSimplexDomain n), x ∈ interior (signedSimplexDomain n) := by
  rw [ae_iff]
  have hmeas : MeasurableSet (interior (signedSimplexDomain n))ᶜ := isOpen_interior.isClosed_compl.measurableSet
  change μ.restrict (signedSimplexDomain n) (interior (signedSimplexDomain n))ᶜ = 0
  rw [Measure.restrict_apply hmeas, inter_comm]
  exact measure_signedSimplexDomain_diff_interior n μ

theorem integral_signedSimplexCount_of_extension (n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure]
    (σ : RawSingularSimplex (Fin n → ℝ) n) (hσ : ∃ L : ℝ≥0, LipschitzWith L σ)
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ∀ x : signedSimplexDomain n, F x.val = σ ((signedSimplexCoordinates n).symm x))
    {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    (∫ y, signedSimplexCount n σ y * g y ∂μ) =
      ∫ x in signedSimplexDomain n, (fderiv ℝ F x).det * g (F x) ∂μ := by
  rw [integral_signedSimplexCount n μ σ hσ hg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_signedSimplexDomain_mem_interior n μ] with x hx
  have he : signedSimplexExtension n σ =ᶠ[𝓝 x] F := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with z hz
    exact ((signedSimplexExtension_spec n σ hσ).2 ⟨z, hz⟩).trans (hF ⟨z, hz⟩).symm
  rw [he.fderiv_eq, he.eq_of_nhds]

end BanachIsometric.SingularPrism
