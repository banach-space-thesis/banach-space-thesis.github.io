import ThesisCommon.Analysis.LpHaarSplit
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Bounded integration and the coefficient functionals of actual Haar vectors.
The estimates hold for every exponent at least one on a probability space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

theorem lpHaarIntegral_norm_le [IsProbabilityMeasure μ] (f : Lp 𝕜 p μ) :
    ‖∫ x, f x ∂μ‖ ≤ ‖f‖ := by
  refine (norm_integral_le_lintegral_norm f).trans ?_
  simp only [ofReal_norm_eq_enorm, ← eLpNorm_one_eq_lintegral_enorm]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le Fact.out (Lp.memLp f).1)

def lpHaarIntegral [IsProbabilityMeasure μ] : Lp 𝕜 p μ →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => by
        rw [integral_congr_ae (Lp.coeFn_add f g)]
        exact integral_add ((Lp.memLp f).integrable Fact.out)
          ((Lp.memLp g).integrable Fact.out)
      map_smul' := fun c f => by
        rw [integral_congr_ae (Lp.coeFn_smul c f)]
        exact integral_smul c f }
    1 (fun f => by simpa only [one_mul] using lpHaarIntegral_norm_le f)

@[simp] theorem lpHaarIntegral_apply [IsProbabilityMeasure μ] (f : Lp 𝕜 p μ) :
    lpHaarIntegral f = ∫ x, f x ∂μ := rfl

theorem norm_lpHaarIntegral_le [IsProbabilityMeasure μ] :
    ‖lpHaarIntegral (𝕜 := 𝕜) (p := p) (μ := μ)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def lpHaarMultiplyValue (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : Lp 𝕜 p μ) : Lp 𝕜 p μ :=
  (((Lp.memLp f).indicator hs).sub ((Lp.memLp f).indicator ht)).toLp
    (s.indicator f - t.indicator f)

theorem lpHaarMultiplyValue_coe (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (f : Lp 𝕜 p μ) :
    lpHaarMultiplyValue s t hs ht f =ᵐ[μ] fun x => lpHaarFunction 𝕜 s t x * f x := by
  refine (MemLp.coeFn_toLp _).trans (Eventually.of_forall fun x => ?_)
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
    simp [lpHaarFunction, hxs, hxt]

theorem lpHaarMultiplyValue_norm_le (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t)
    (f : Lp 𝕜 p μ) : ‖lpHaarMultiplyValue s t hs ht f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  apply eLpNorm_mono_ae
  filter_upwards [lpHaarMultiplyValue_coe s t hs ht f] with x hx
  rw [hx, norm_mul, lpHaarFunction_norm s t hst]
  by_cases hx : x ∈ s ∪ t <;> simp [hx]

def lpHaarMultiply (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous
    { toFun := lpHaarMultiplyValue s t hs ht
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [lpHaarMultiplyValue_coe s t hs ht (f + g),
          lpHaarMultiplyValue_coe s t hs ht f, lpHaarMultiplyValue_coe s t hs ht g,
          Lp.coeFn_add f g, Lp.coeFn_add (lpHaarMultiplyValue s t hs ht f)
            (lpHaarMultiplyValue s t hs ht g)] with x h₁ h₂ h₃ h₄ h₅
        simp only [Pi.add_apply] at h₄ h₅
        rw [h₁, h₄, h₅, h₂, h₃, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [lpHaarMultiplyValue_coe s t hs ht (c • f),
          lpHaarMultiplyValue_coe s t hs ht f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (lpHaarMultiplyValue s t hs ht f)] with x h₁ h₂ h₃ h₄
        simp only [Pi.smul_apply] at h₃ h₄
        simp only [h₁, h₂, h₃, h₄, smul_eq_mul, RingHom.id_apply]
        ring }
    1 (fun f => by simpa only [one_mul] using lpHaarMultiplyValue_norm_le s t hs ht hst f)

theorem lpHaarMultiply_coe (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (f : Lp 𝕜 p μ) :
    lpHaarMultiply s t hs ht hst f =ᵐ[μ] fun x => lpHaarFunction 𝕜 s t x * f x :=
  lpHaarMultiplyValue_coe s t hs ht f

theorem norm_lpHaarMultiply_le (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    ‖lpHaarMultiply (𝕜 := 𝕜) (p := p) (μ := μ) s t hs ht hst‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def lpHaarCoefficient [IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) : Lp 𝕜 p μ →L[𝕜] 𝕜 :=
  ((μ.real (s ∪ t) : 𝕜)⁻¹) • (lpHaarIntegral.comp (lpHaarMultiply s t hs ht hst))

theorem lpHaarCoefficient_apply [IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (f : Lp 𝕜 p μ) :
    lpHaarCoefficient s t hs ht hst f =
      (μ.real (s ∪ t) : 𝕜)⁻¹ * ∫ x, lpHaarFunction 𝕜 s t x * f x ∂μ := by
  change (μ.real (s ∪ t) : 𝕜)⁻¹ * (∫ x, lpHaarMultiply s t hs ht hst f x ∂μ) = _
  rw [integral_congr_ae (lpHaarMultiply_coe s t hs ht hst f)]

theorem lpHaarCoefficient_self [IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (hm : μ (s ∪ t) ≠ 0) :
    lpHaarCoefficient s t hs ht hst (lpHaarVector (μ := μ) 𝕜 p s t hs ht) = 1 := by
  rw [lpHaarCoefficient_apply]
  have heq : (fun x => lpHaarFunction 𝕜 s t x * lpHaarVector (μ := μ) 𝕜 p s t hs ht x)
      =ᵐ[μ] (s ∪ t).indicator (fun _ => (1 : 𝕜)) := by
    filter_upwards [lpHaarVector_coe (𝕜 := 𝕜) (μ := μ) (p := p) s t hs ht] with x hx
    rw [hx]
    by_cases hxs : x ∈ s
    · have hxt : x ∉ t := fun hxt => Set.disjoint_left.mp hst hxs hxt
      simp [lpHaarFunction, hxs, hxt]
    · by_cases hxt : x ∈ t <;> simp [lpHaarFunction, hxs, hxt]
  rw [integral_congr_ae heq, integral_indicator_const _ (hs.union ht)]
  simp only [Algebra.smul_def, RCLike.algebraMap_eq_ofReal, mul_one]
  apply inv_mul_cancel₀
  exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hm, measure_ne_top μ (s ∪ t)⟩)

theorem norm_lpHaarCoefficient_le [IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    ‖lpHaarCoefficient (𝕜 := 𝕜) (p := p) (μ := μ) s t hs ht hst‖ ≤
      (μ.real (s ∪ t))⁻¹ := by
  unfold lpHaarCoefficient
  rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg measureReal_nonneg]
  calc
    _ ≤ (μ.real (s ∪ t))⁻¹ * (‖lpHaarIntegral (𝕜 := 𝕜) (p := p) (μ := μ)‖ *
        ‖lpHaarMultiply (𝕜 := 𝕜) (p := p) (μ := μ) s t hs ht hst‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)
    _ ≤ (μ.real (s ∪ t))⁻¹ * (1 * 1) := by
      gcongr
      · exact norm_lpHaarIntegral_le
      · exact norm_lpHaarMultiply_le s t hs ht hst
    _ = _ := by simp

end ThesisCommon
