import ThesisCommon.Analysis.LebesgueLpRestrictions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Haar differences on genuine `Lp` spaces.  Disjoint measurable children
give the exact norm of their parent indicator; equally sized children give
cancellation.  These statements work over both real and complex scalars. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

def lpHaarFunction (𝕜 : Type*) [RCLike 𝕜] (s t : Set α) : α → 𝕜 :=
  s.indicator (fun _ => (1 : 𝕜)) - t.indicator (fun _ => (1 : 𝕜))

def lpHaarVector (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) : Lp 𝕜 p μ :=
  indicatorConstLp p hs (measure_ne_top μ s) 1 -
    indicatorConstLp p ht (measure_ne_top μ t) 1

theorem lpHaarVector_coe (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    lpHaarVector (μ := μ) 𝕜 p s t hs ht =ᵐ[μ] lpHaarFunction 𝕜 s t := by
  exact (Lp.coeFn_sub _ _).trans
    (Filter.EventuallyEq.sub indicatorConstLp_coeFn indicatorConstLp_coeFn)

theorem lpHaarFunction_norm (s t : Set α) (hst : Disjoint s t) (x : α) :
    ‖lpHaarFunction 𝕜 s t x‖ = ‖(s ∪ t).indicator (fun _ => (1 : 𝕜)) x‖ := by
  by_cases hs : x ∈ s
  · have ht : x ∉ t := fun ht => Set.disjoint_left.mp hst hs ht
    simp [lpHaarFunction, hs, ht]
  · by_cases ht : x ∈ t <;> simp [lpHaarFunction, hs, ht]

theorem lpHaarVector_norm_eq_indicator (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    ‖lpHaarVector (μ := μ) 𝕜 p s t hs ht‖ =
      ‖indicatorConstLp p (hs.union ht) (measure_ne_top μ (s ∪ t)) (1 : 𝕜)‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [lpHaarVector_coe (𝕜 := 𝕜) (μ := μ) (p := p) s t hs ht,
    (indicatorConstLp_coeFn (p := p) (hs := hs.union ht)
      (hμs := measure_ne_top μ (s ∪ t)) (c := (1 : 𝕜)))] with x h₁ h₂
  rw [h₁, h₂]
  exact lpHaarFunction_norm s t hst x

theorem lpHaarVector_norm (hp : p ≠ ∞) (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    ‖lpHaarVector (μ := μ) 𝕜 p s t hs ht‖ =
      μ.real (s ∪ t) ^ (1 / p.toReal) := by
  rw [lpHaarVector_norm_eq_indicator s t hs ht hst,
    norm_indicatorConstLp (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp,
    norm_one, one_mul]

theorem lpHaarFunction_integrable (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Integrable (lpHaarFunction 𝕜 s t) μ :=
  ((integrable_const (1 : 𝕜)).indicator hs).sub
    ((integrable_const (1 : 𝕜)).indicator ht)

theorem lpHaarVector_integrable (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Integrable (lpHaarVector (μ := μ) 𝕜 p s t hs ht : α → 𝕜) μ :=
  (lpHaarFunction_integrable s t hs ht).congr
    (lpHaarVector_coe (𝕜 := 𝕜) (μ := μ) (p := p) s t hs ht).symm

theorem lpHaarFunction_integral (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫ x, lpHaarFunction 𝕜 s t x ∂μ = (μ.real s : 𝕜) - (μ.real t : 𝕜) := by
  unfold lpHaarFunction
  simp only [Pi.sub_apply]
  rw [integral_sub ((integrable_const (1 : 𝕜)).indicator hs)
    ((integrable_const (1 : 𝕜)).indicator ht), integral_indicator_const _ hs,
    integral_indicator_const _ ht]
  simp only [Algebra.smul_def, RCLike.algebraMap_eq_ofReal, mul_one]

theorem lpHaarVector_integral (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫ x, lpHaarVector (μ := μ) 𝕜 p s t hs ht x ∂μ =
      (μ.real s : 𝕜) - (μ.real t : 𝕜) :=
  (integral_congr_ae (lpHaarVector_coe s t hs ht)).trans
    (lpHaarFunction_integral s t hs ht)

theorem lpHaarVector_integral_zero (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hm : μ s = μ t) :
    ∫ x, lpHaarVector (μ := μ) 𝕜 p s t hs ht x ∂μ = 0 := by
  rw [lpHaarVector_integral s t hs ht]
  simp only [measureReal_def, hm, sub_self]

theorem lpHaarVector_zero_off (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∀ᵐ x ∂μ, x ∉ s ∪ t → lpHaarVector (μ := μ) 𝕜 p s t hs ht x = 0 := by
  filter_upwards [lpHaarVector_coe (𝕜 := 𝕜) (μ := μ) (p := p) s t hs ht] with x hx h
  rw [hx]
  simp only [mem_union, not_or] at h
  simp [lpHaarFunction, h.1, h.2]

end ThesisCommon
