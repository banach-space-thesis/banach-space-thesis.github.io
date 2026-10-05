import ThesisCommon.Analysis.RegularMeasureCutoff
import ThesisCommon.Analysis.ContinuousMapRieszVariation
import ThesisCommon.Analysis.ContinuousMapDualAL

/-! Order determination by continuous positive tests for finite regular measures,
and the actual Riesz measure of a positive continuous functional. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

theorem regularMeasure_le_of_continuous_integral_le (μ ν : Measure K)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.Regular] [ν.Regular]
    (h : ∀ f : C(K, ℝ), 0 ≤ f → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  have hopen : ∀ U : Set K, IsOpen U → μ U ≤ ν U := by
    intro U hU
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ U) (measure_ne_top ν U)).mp
    apply le_of_forall_lt
    intro r hr
    obtain ⟨f, hf, hfs, hfr⟩ := exists_continuousMap_open_mass_test μ hU hr
    have htest := h f (fun x => (hf x).1)
    have hupper : (∫ x, f x ∂ν) ≤ ν.real U := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfs]
      calc
        (∫ x in U, f x ∂ν) ≤ ∫ x in U, (1 : ℝ) ∂ν :=
          integral_mono (continuousMap_integrable_finite (ν.restrict U) f)
            (integrable_const 1) (fun x => (hf x).2)
        _ = ν.real U := by simp
    exact hfr.trans_le (htest.trans hupper)
  apply Measure.le_iff.mpr
  intro A hA
  rw [A.measure_eq_iInf_isOpen ν]
  exact le_iInf fun U => le_iInf fun hAU => le_iInf fun hU =>
    (measure_mono hAU).trans (hopen U hU)

theorem continuousMapRieszMeasure_le_iff
    (Λ Γ : C(K, ℝ) →ₚ[ℝ] ℝ) :
    continuousMapRieszMeasure Λ ≤ continuousMapRieszMeasure Γ ↔
      ∀ f : C(K, ℝ), 0 ≤ f → Λ f ≤ Γ f := by
  constructor
  · intro h f hf
    have hi := integral_mono_measure h (Filter.Eventually.of_forall hf)
      (continuousMap_integrable_finite (continuousMapRieszMeasure Γ) f)
    change (∫ x, f x ∂continuousMapRieszMeasure Λ) ≤
      ∫ x, f x ∂continuousMapRieszMeasure Γ at hi
    simpa only [integral_continuousMapRieszMeasure] using hi
  · intro h
    apply regularMeasure_le_of_continuous_integral_le
    simpa only [integral_continuousMapRieszMeasure] using h

def positiveContinuousMapRiesz (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) : Measure K :=
  continuousMapRieszMeasure
    (PositiveLinearMap.mk₀ φ.toLinearMap ((operator_nonneg_iff φ).mp hφ))

instance positiveContinuousMapRiesz_finite (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) :
    IsFiniteMeasure (positiveContinuousMapRiesz φ hφ) := by
  unfold positiveContinuousMapRiesz
  infer_instance

instance positiveContinuousMapRiesz_regular (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) :
    (positiveContinuousMapRiesz φ hφ).Regular := by
  unfold positiveContinuousMapRiesz
  infer_instance

theorem integral_positiveContinuousMapRiesz (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ)
    (f : C(K, ℝ)) : (∫ x, f x ∂positiveContinuousMapRiesz φ hφ) = φ f :=
  integral_continuousMapRieszMeasure _ f

theorem positiveContinuousMapRiesz_mass (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) :
    (positiveContinuousMapRiesz φ hφ).real univ = φ 1 :=
  continuousMapRieszMeasure_mass _

theorem positiveContinuousMapRiesz_mass_norm (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) :
    (positiveContinuousMapRiesz φ hφ).real univ = ‖φ‖ :=
  (positiveContinuousMapRiesz_mass φ hφ).trans (norm_positive_continuousMapDual φ hφ).symm

theorem positiveContinuousMapRiesz_le_iff
    (φ ψ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ) :
    positiveContinuousMapRiesz φ hφ ≤ positiveContinuousMapRiesz ψ hψ ↔ φ ≤ ψ := by
  rw [positiveContinuousMapRiesz, positiveContinuousMapRiesz,
    continuousMapRieszMeasure_le_iff, operator_le_iff]
  rfl

theorem positiveContinuousMapRiesz_injective
    (φ ψ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ)
    (h : positiveContinuousMapRiesz φ hφ = positiveContinuousMapRiesz ψ hψ) : φ = ψ :=
  le_antisymm ((positiveContinuousMapRiesz_le_iff φ ψ hφ hψ).mp h.le)
    ((positiveContinuousMapRiesz_le_iff ψ φ hψ hφ).mp h.ge)

end ThesisCommon
