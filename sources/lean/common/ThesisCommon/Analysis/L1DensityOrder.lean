import ThesisCommon.Analysis.L1DensityOperatorOrder

/-! A strictly positive change of density gives an actual order-preserving
L1 isometry in both directions. No finiteness assumption is needed here. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ≥0}

theorem lOneWithDensityEquiv_nonneg_iff (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (f : Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) :
    0 ≤ lOneWithDensityEquiv hg hpos f ↔ 0 ≤ f := by
  constructor
  · intro hf
    apply (Lp.coeFn_nonneg f).mp
    apply (ae_withDensity_coe_iff_of_pos hg hpos).mpr
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf, withDensitySMulLI_coe hg f, hpos]
      with x hfx hcoe hgx
    change 0 ≤ f x
    change 0 ≤ withDensitySMulLI μ hg f x at hfx
    rw [hcoe] at hfx
    have hgx' : 0 < (g x : ℝ) := by exact_mod_cast hgx
    nlinarith
  · exact withDensitySMulLI_nonneg hg f

end ThesisCommon
