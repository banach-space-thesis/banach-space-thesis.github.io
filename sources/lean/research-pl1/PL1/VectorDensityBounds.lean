import PL1.RNPBridge
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Pointwise bounds for vector-measure densities -/

noncomputable section
universe u v w
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.VectorDensityBounds

variable {Ω : Type w} [MeasurableSpace Ω]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E₀ : Type v} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]

omit [NormedSpace ℝ E] in
/-- Null-set vanishing of a vector measure implies absolute continuity of its total variation. -/
theorem variation_absolutelyContinuous (μ : Measure Ω) (ν : VectorMeasure Ω E)
    (hAC : ∀ A : Set Ω, MeasurableSet A → μ A = 0 → ν A = 0) :
    ν.variation ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hμA
  apply (VectorMeasure.variation_apply_eq_zero hA).mpr
  intro B hBA hB
  exact hAC B hB (measure_mono_null hBA hμA)

/-- Domination of positive measures with density yields pointwise domination of their densities. -/
theorem ae_le_of_withDensity_le (μ : Measure Ω) [SigmaFinite μ]
    {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f μ)
    (h : μ.withDensity f ≤ μ.withDensity g) : f ≤ᵐ[μ] g := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf
  intro A hA _
  rw [← withDensity_apply f hA, ← withDensity_apply g hA]
  exact h A

/-- A finite absolutely continuous measure dominating the variation controls a Bochner
density pointwise by its ordinary Radon–Nikodym derivative. -/
theorem ae_norm_density_le_rnDeriv [CompleteSpace E]
    (μ τ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure τ]
    (hτ : τ ≪ μ) {g : Ω → E} (hg : Integrable g μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : (μ.withDensityᵥ g).variation ≤ ENNReal.ofReal C • τ) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ C * (τ.rnDeriv μ x).toReal := by
  have hwith : μ.withDensity (fun x => ‖g x‖ₑ) ≤
      μ.withDensity (ENNReal.ofReal C • τ.rnDeriv μ) := by
    rw [withDensity_smul _ (τ.measurable_rnDeriv μ), Measure.withDensity_rnDeriv_eq τ μ hτ]
    rw [← Measure.variation_withDensityᵥ hg]
    exact hbound
  have hae := ae_le_of_withDensity_le μ hg.aestronglyMeasurable.enorm hwith
  filter_upwards [hae, Measure.rnDeriv_lt_top τ μ] with x hx hfinite
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne) hx
  simpa only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, toReal_enorm] using hreal

/-- Applying a bounded linear map to a vector measure gives a uniformly dominated density. -/
theorem ae_norm_map_density_le_rnDeriv [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : VectorMeasure Ω E₀)
    [IsFiniteMeasure ν.variation]
    (hAC : ∀ A : Set Ω, MeasurableSet A → μ A = 0 → ν A = 0)
    (T : E₀ →L[ℝ] E) {g : Ω → E} (hg : Integrable g μ)
    (hrep : μ.withDensityᵥ g = RNPBridge.mapVectorMeasure T ν)
    (C : ℝ) (hC : 0 ≤ C) (hT : ‖T‖ ≤ C) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ C * (ν.variation.rnDeriv μ x).toReal := by
  apply ae_norm_density_le_rnDeriv μ ν.variation
    (variation_absolutelyContinuous μ ν hAC) hg C hC
  rw [hrep]
  apply (RNPBridge.variation_mapVectorMeasure_le T ν).trans
  intro A
  simp only [Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ zero_le
  simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hT

end PL1.VectorDensityBounds
