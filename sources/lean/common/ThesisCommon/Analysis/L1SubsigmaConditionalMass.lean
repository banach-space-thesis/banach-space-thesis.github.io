import ThesisCommon.Analysis.L1SubsigmaProjection
import ThesisCommon.Analysis.L1AdjointOne
import ThesisCommon.LpCut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! Positivity, faithful positive mass, and localization for the actual L1
conditional-expectation projection.  These identities concern the genuine
projection, including finite measures of total mass zero. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {X : Type*} {m₀ : MeasurableSpace X} (μ : @Measure X m₀) [IsFiniteMeasure μ]
variable {m : MeasurableSpace X} (hm : m ≤ m₀)

theorem lOneSubsigmaProjection_coe_condExp (f : Lp ℝ 1 μ) :
    (lOneSubsigmaProjection μ hm f : X → ℝ) =ᵐ[μ] μ[(f : X → ℝ)|m] := by
  have h := condExp_ae_eq_condExpL1CLM hm (L1.integrable_coeFn f)
  rw [Integrable.toL1_coeFn] at h
  exact h.symm

theorem lOneSubsigmaProjection_mono : Monotone (lOneSubsigmaProjection μ hm) := by
  intro f g hfg
  apply (Lp.coeFn_le _ _).mp
  exact (lOneSubsigmaProjection_coe_condExp μ hm f).trans_le
    ((condExp_mono (L1.integrable_coeFn f) (L1.integrable_coeFn g)
      ((Lp.coeFn_le _ _).mpr hfg)).trans_eq
      (lOneSubsigmaProjection_coe_condExp μ hm g).symm)

theorem lOneSubsigmaProjection_nonneg {f : Lp ℝ 1 μ} (hf : 0 ≤ f) :
    0 ≤ lOneSubsigmaProjection μ hm f := by
  simpa only [map_zero] using lOneSubsigmaProjection_mono μ hm hf

theorem integral_lOneSubsigmaProjection (f : Lp ℝ 1 μ) :
    ∫ x, lOneSubsigmaProjection μ hm f x ∂μ = ∫ x, f x ∂μ := by
  simpa only [Measure.restrict_univ] using
    (setIntegral_condExpL1CLM (hm := hm) f (MeasurableSet.univ : MeasurableSet[m] univ))

theorem norm_lOneSubsigmaProjection_of_nonneg {f : Lp ℝ 1 μ} (hf : 0 ≤ f) :
    ‖lOneSubsigmaProjection μ hm f‖ = ‖f‖ := by
  rw [@lOne_norm_eq_integral_of_nonneg X m₀ μ _ (lOneSubsigmaProjection_nonneg μ hm hf),
    integral_lOneSubsigmaProjection, @lOne_norm_eq_integral_of_nonneg X m₀ μ f hf]

theorem lOneSubsigmaProjection_eq_zero_iff_of_nonneg {f : Lp ℝ 1 μ} (hf : 0 ≤ f) :
    lOneSubsigmaProjection μ hm f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [← norm_lOneSubsigmaProjection_of_nonneg μ hm hf, h, norm_zero]
  · rintro rfl
    exact map_zero _

theorem lOneSubsigmaProjection_cut (A : Set X) (hA : MeasurableSet[m] A) (f : Lp ℝ 1 μ) :
    lOneSubsigmaProjection μ hm (@lpCut ℝ _ X m₀ μ 1 A (hm A hA) f) =
      @lpCut ℝ _ X m₀ μ 1 A (hm A hA) (lOneSubsigmaProjection μ hm f) := by
  apply Lp.ext
  calc
    (lOneSubsigmaProjection μ hm (@lpCut ℝ _ X m₀ μ 1 A (hm A hA) f) : X → ℝ) =ᵐ[μ]
        μ[(@lpCut ℝ _ X m₀ μ 1 A (hm A hA) f : X → ℝ)|m] :=
      lOneSubsigmaProjection_coe_condExp μ hm _
    _ =ᵐ[μ] μ[A.indicator (f : X → ℝ)|m] := condExp_congr_ae (@lpCut_coe ℝ _ X m₀ μ 1 A (hm A hA) f)
    _ =ᵐ[μ] A.indicator (μ[(f : X → ℝ)|m]) := condExp_indicator (L1.integrable_coeFn f) hA
    _ =ᵐ[μ] A.indicator (lOneSubsigmaProjection μ hm f : X → ℝ) := by
      filter_upwards [(lOneSubsigmaProjection_coe_condExp μ hm f).symm] with x hx
      by_cases h : x ∈ A <;> simp [h, hx]
    _ =ᵐ[μ] (@lpCut ℝ _ X m₀ μ 1 A (hm A hA) (lOneSubsigmaProjection μ hm f) : X → ℝ) :=
      (@lpCut_coe ℝ _ X m₀ μ 1 A (hm A hA) _).symm

end ThesisCommon

