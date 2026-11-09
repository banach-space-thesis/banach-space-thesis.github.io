import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Normalised uniform measures and linear changes of coordinates

Normalisation cancels the Haar/Lebesgue determinant factor. This is the
measure-level identity underlying the transformation rule for every moment,
including odd moments, of a not necessarily symmetric star body.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped ENNReal

/-- Normalised restriction to the body; the zero/infinite-mass cases are left
defined by the standard extended-nonnegative arithmetic. Probability conclusions
below explicitly require finite positive mass. -/
noncomputable def normalizedRestriction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) : Measure X := (μ S)⁻¹ • μ.restrict S

theorem normalizedRestriction_isProbabilityMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (h0 : μ S ≠ 0) (hf : μ S ≠ ∞) :
    IsProbabilityMeasure (normalizedRestriction μ S) := by
  constructor
  simp [normalizedRestriction, ENNReal.inv_mul_cancel h0 hf]

theorem normalizedRestriction_compl {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S) :
    normalizedRestriction μ S Sᶜ = 0 := by
  simp [normalizedRestriction, Measure.restrict_apply hS.compl]

theorem normalizedRestriction_smul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (c : ℝ≥0∞) (h0 : c ≠ 0) (hf : c ≠ ∞) :
    normalizedRestriction (c • μ) S = normalizedRestriction μ S := by
  unfold normalizedRestriction
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_smul, smul_smul]
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl hf)]
  have hcancel : c⁻¹ * (μ S)⁻¹ * c = (μ S)⁻¹ := by
    calc
      c⁻¹ * (μ S)⁻¹ * c = (c⁻¹ * c) * (μ S)⁻¹ := by ac_rfl
      _ = (μ S)⁻¹ := by rw [ENNReal.inv_mul_cancel h0 hf, one_mul]
  rw [hcancel]

/-- Exact normalised restriction transport under a measurable bijection. -/
theorem normalizedRestriction_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (S : Set X) :
    (normalizedRestriction μ S).map e = normalizedRestriction (μ.map e) (e '' S) := by
  have hmass : (μ.map e) (e '' S) = μ S := by
    rw [e.map_apply, e.injective.preimage_image]
  have hrestrict := e.measurableEmbedding.restrict_map μ (e '' S)
  rw [e.injective.preimage_image] at hrestrict
  unfold normalizedRestriction
  rw [Measure.map_smul, hmass, hrestrict]

/-- Integration against the uniform probability measure is the paper's
normalised set integral, including the prescribed origin without centring. -/
theorem integral_normalizedRestriction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (f : X → ℝ) :
    (∫ x, f x ∂normalizedRestriction μ S) = (μ.real S)⁻¹ * ∫ x in S, f x ∂μ := by
  simp only [normalizedRestriction, integral_smul_measure, ENNReal.toReal_inv,
    measureReal_def, smul_eq_mul]

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The determinant factor in Haar change of variables cancels entirely for
the uniform measures on a body and its real-linear image. -/
theorem normalizedRestriction_map_linearEquiv (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] E) (S : Set E) :
    (normalizedRestriction μ S).map e = normalizedRestriction μ (e '' S) := by
  have hd : LinearMap.det e.toLinearEquiv.toLinearMap ≠ 0 :=
    e.toLinearEquiv.isUnit_det'.ne_zero
  let c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹|
  have h0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hd))).ne'
  have hf : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hmap : μ.map e = c • μ := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd
  calc
    (normalizedRestriction μ S).map e = normalizedRestriction (μ.map e) (e '' S) :=
      normalizedRestriction_map μ e.toHomeomorph.toMeasurableEquiv S
    _ = normalizedRestriction μ (e '' S) := by
      rw [hmap]
      exact normalizedRestriction_smul μ (e '' S) c h0 hf

end Linear

end BanachIsometric
