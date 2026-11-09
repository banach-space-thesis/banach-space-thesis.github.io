import SurveyStatements.P5HaarCoordinates
import SurveyStatements.P5Support.LpHaarBiorthogonal

/-! Biorthogonality of the genuine product-Haar vectors. The interval
convention used by the supporting proofs is identified modulo null endpoints. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem haarSign_congr_ae {s t s' t' : Set ℝ}
    (hs : s =ᵐ[unitIntervalMeasure] s') (ht : t =ᵐ[unitIntervalMeasure] t') :
    P5Support.lpHaarFunction 𝕜 s t =ᵐ[unitIntervalMeasure]
      P5Support.lpHaarFunction 𝕜 s' t' := by
  filter_upwards [hs, ht] with x hsx htx
  change (x ∈ s) = (x ∈ s') at hsx
  change (x ∈ t) = (x ∈ t') at htx
  have hl : s.indicator (fun _ => (1 : 𝕜)) x = s'.indicator (fun _ => (1 : 𝕜)) x := by
    by_cases h : x ∈ s
    · have h' : x ∈ s' := hsx.mp h
      rw [indicator_of_mem h, indicator_of_mem h']
    · have h' : x ∉ s' := fun hx => h (hsx.mpr hx)
      rw [indicator_of_notMem h, indicator_of_notMem h']
  have hr : t.indicator (fun _ => (1 : 𝕜)) x = t'.indicator (fun _ => (1 : 𝕜)) x := by
    by_cases h : x ∈ t
    · have h' : x ∈ t' := htx.mp h
      rw [indicator_of_mem h, indicator_of_mem h']
    · have h' : x ∉ t' := fun hx => h (htx.mpr hx)
      rw [indicator_of_notMem h, indicator_of_notMem h']
  exact congrArg₂ (· - ·) hl hr

theorem haarCoordinate_congr_ae {s t s' t' : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hs' : MeasurableSet s') (ht' : MeasurableSet t')
    (hd : Disjoint s t) (hd' : Disjoint s' t')
    (hsae : s =ᵐ[unitIntervalMeasure] s') (htae : t =ᵐ[unitIntervalMeasure] t') :
    P5Support.lpHaarCoefficient (𝕜 := 𝕜) (p := p) (μ := unitIntervalMeasure) s t hs ht hd =
      P5Support.lpHaarCoefficient (μ := unitIntervalMeasure) s' t' hs' ht' hd' := by
  apply ContinuousLinearMap.ext
  intro f
  rw [P5Support.lpHaarCoefficient_apply, P5Support.lpHaarCoefficient_apply]
  have hmeasure := measure_congr (hsae.union htae)
  simp only [Measure.real, hmeasure]
  congr 1
  apply integral_congr_ae
  exact (haarSign_congr_ae hsae htae).mul (ae_eq_refl f)

theorem haarVector_congr_ae {s t s' t' : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hs' : MeasurableSet s') (ht' : MeasurableSet t')
    (hsae : s =ᵐ[unitIntervalMeasure] s') (htae : t =ᵐ[unitIntervalMeasure] t') :
    P5Support.lpHaarVector (μ := unitIntervalMeasure) 𝕜 p s t hs ht =
      P5Support.lpHaarVector (μ := unitIntervalMeasure) 𝕜 p s' t' hs' ht' := by
  apply Lp.ext
  exact (P5Support.lpHaarVector_coe s t hs ht).trans
    ((haarSign_congr_ae hsae htae).trans (P5Support.lpHaarVector_coe s' t' hs' ht').symm)

theorem haarLeft_supportCell (I : DyadicIndex) :
    P5Support.lpHaarCell (I.1 + 1) (2 * I.2.val) =
      Ioc (dyadicStart I) (dyadicMiddle I) := by
  unfold P5Support.lpHaarCell
  have hstart : ((2 * I.2.val : ℕ) : ℝ) * P5Support.intervalLpDyadicRadius (I.1 + 1) =
      dyadicStart I := by
    simp [P5Support.intervalLpDyadicRadius, dyadicStart, pow_succ,
      one_div_pow, div_eq_mul_inv]
    <;> ring
  have hend : (((2 * I.2.val : ℕ) : ℝ) + 1) *
      P5Support.intervalLpDyadicRadius (I.1 + 1) = dyadicMiddle I := by
    simp [P5Support.intervalLpDyadicRadius, dyadicMiddle, pow_succ,
      one_div_pow, div_eq_mul_inv]
    <;> ring
  rw [hstart, hend]

theorem haarRight_supportCell (I : DyadicIndex) :
    P5Support.lpHaarCell (I.1 + 1) (2 * I.2.val + 1) =
      Ioc (dyadicMiddle I) (dyadicEnd I) := by
  unfold P5Support.lpHaarCell
  have hstart : ((2 * I.2.val + 1 : ℕ) : ℝ) *
      P5Support.intervalLpDyadicRadius (I.1 + 1) = dyadicMiddle I := by
    simp [P5Support.intervalLpDyadicRadius, dyadicMiddle, pow_succ,
      one_div_pow, div_eq_mul_inv]
    <;> ring
  have hend : (((2 * I.2.val + 1 : ℕ) : ℝ) + 1) *
      P5Support.intervalLpDyadicRadius (I.1 + 1) = dyadicEnd I := by
    simp [P5Support.intervalLpDyadicRadius, dyadicEnd, pow_succ,
      one_div_pow, div_eq_mul_inv]
    <;> ring
  rw [hstart, hend]

theorem haarLeft_supportCell_ae (I : DyadicIndex) :
    dyadicLeft I =ᵐ[unitIntervalMeasure] P5Support.lpHaarCell (I.1 + 1) (2 * I.2.val) := by
  rw [haarLeft_supportCell]
  exact ae_restrict_of_ae (Ico_ae_eq_Ioc (μ := volume))

theorem haarRight_supportCell_ae (I : DyadicIndex) :
    dyadicRight I =ᵐ[unitIntervalMeasure]
      P5Support.lpHaarCell (I.1 + 1) (2 * I.2.val + 1) := by
  rw [haarRight_supportCell]
  exact ae_restrict_of_ae (Ico_ae_eq_Ioc (μ := volume))

theorem dyadicHaar_eq_support (I : DyadicIndex) :
    dyadicHaar 𝕜 p I = P5Support.lpHaarDyadic 𝕜 ⟨p, Fact.out⟩ I.1 I.2.val :=
  haarVector_congr_ae _ _ _ _ (haarLeft_supportCell_ae I) (haarRight_supportCell_ae I)

theorem dyadicHaarCoordinate_eq_support (I : DyadicIndex) :
    dyadicHaarCoordinate 𝕜 p I =
      P5Support.lpHaarDyadicCoefficient 𝕜 ⟨p, Fact.out⟩ I.1 I.2 :=
  haarCoordinate_congr_ae _ _ _ _ _ _
    (haarLeft_supportCell_ae I) (haarRight_supportCell_ae I)

theorem dyadicHaarCoordinate_biorthogonal (hp : p ≠ ∞) (I K : DyadicIndex) :
    dyadicHaarCoordinate 𝕜 p I (dyadicHaar 𝕜 p K) = if I = K then 1 else 0 := by
  rw [dyadicHaarCoordinate_eq_support, dyadicHaar_eq_support]
  simpa [P5Support.lpHaarRawCoordinate, P5Support.lpHaarRawVector] using
    P5Support.lpHaarRaw_biorthogonal 𝕜 ⟨p, Fact.out⟩ hp (some I) (some K)

theorem productHaarCoordinate_biorthogonal (hp : p ≠ ∞)
    (I J K L : DyadicIndex) :
    productHaarCoordinate 𝕜 p I J (productHaar 𝕜 p K L) =
      if (I, J) = (K, L) then 1 else 0 := by
  rw [productHaar, productHaarCoordinate_tensor, dyadicHaarCoordinate_biorthogonal
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞), dyadicHaarCoordinate_biorthogonal hp]
  by_cases hI : I = K <;> by_cases hJ : J = L <;> simp [hI, hJ]

end SurveyStatements.P5
