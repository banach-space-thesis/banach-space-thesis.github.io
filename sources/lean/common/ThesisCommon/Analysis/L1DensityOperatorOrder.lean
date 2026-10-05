import ThesisCommon.Analysis.L1DensityEquiv
import ThesisCommon.Analysis.L1OperatorLattice

/-! A strictly positive change of measure is an order isomorphism on L1
and on actual bounded operators by precomposition. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} {g : X → ℝ≥0}

theorem withDensitySMulLI_nonneg_iff (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (f : Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) :
    0 ≤ withDensitySMulLI μ hg f ↔ 0 ≤ f := by
  refine ⟨?_, withDensitySMulLI_nonneg hg f⟩
  intro hf
  apply (Lp.coeFn_nonneg f).mp
  apply (ae_withDensity_coe_iff_of_pos hg hpos).mpr
  filter_upwards [withDensitySMulLI_coe hg f,
    (Lp.coeFn_nonneg _).mpr hf, hpos] with x hx hfx hxpos
  rw [hx] at hfx
  exact nonneg_of_mul_nonneg_right hfx (by exact_mod_cast hxpos)

theorem lOneWithDensityEquiv_symm_nonneg (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (f : Lp ℝ 1 μ) (hf : 0 ≤ f) : 0 ≤ (lOneWithDensityEquiv hg hpos).symm f := by
  apply (withDensitySMulLI_nonneg_iff hg hpos _).mp
  change 0 ≤ (lOneWithDensityEquiv hg hpos) ((lOneWithDensityEquiv hg hpos).symm f)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hf

def lOneWithDensityOperatorOrderIso (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) ≃o
      (Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞))) →L[ℝ] Lp ℝ 1 ν) where
  toFun T := T.comp (withDensitySMulLI μ hg).toContinuousLinearMap
  invFun T := T.comp (lOneWithDensityEquiv hg hpos).symm.toLinearIsometry.toContinuousLinearMap
  left_inv T := by
    apply ContinuousLinearMap.ext
    intro f
    change T ((lOneWithDensityEquiv hg hpos) ((lOneWithDensityEquiv hg hpos).symm f)) = T f
    rw [LinearIsometryEquiv.apply_symm_apply]
  right_inv T := by
    apply ContinuousLinearMap.ext
    intro f
    change T ((lOneWithDensityEquiv hg hpos).symm ((lOneWithDensityEquiv hg hpos) f)) = T f
    rw [LinearIsometryEquiv.symm_apply_apply]
  map_rel_iff' := by
    intro S T
    constructor
    · intro h f hf
      have ht := h _ (lOneWithDensityEquiv_symm_nonneg hg hpos f hf)
      change S ((lOneWithDensityEquiv hg hpos) ((lOneWithDensityEquiv hg hpos).symm f)) ≤
        T ((lOneWithDensityEquiv hg hpos) ((lOneWithDensityEquiv hg hpos).symm f)) at ht
      simpa only [LinearIsometryEquiv.apply_symm_apply] using ht
    · intro h f hf
      exact h _ (withDensitySMulLI_nonneg hg f hf)

@[simp] theorem lOneWithDensityOperatorOrderIso_zero
    (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    lOneWithDensityOperatorOrderIso (ν := ν) hg hpos 0 = 0 := by ext f; rfl

end ThesisCommon
