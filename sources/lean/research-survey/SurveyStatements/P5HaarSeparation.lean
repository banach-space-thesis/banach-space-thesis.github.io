import SurveyStatements.P5HaarBiorthogonal
import SurveyStatements.P5Support.LpHaarRootMean

/-! The actual Haar integral coordinates separate scalar zero-mean functions
and the doubly cancellative mixed Bochner space. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem scalarHaarCoordinates_eq_zero (hp : p ≠ ∞)
    (f : Lp 𝕜 p unitIntervalMeasure)
    (hmean : probabilityLpMean (𝕜 := 𝕜) f = 0)
    (hcoeff : ∀ I, dyadicHaarCoordinate 𝕜 p I f = 0) : f = 0 := by
  let q : P5Support.BanachExponent := ⟨p, Fact.out⟩
  have hint : probabilityLpIntegral (𝕜 := 𝕜) f = 0 := by
    have h := congrArg (probabilityLpIntegral (𝕜 := 𝕜) (E := 𝕜)) hmean
    rw [probabilityLpMean_apply, probabilityLpIntegral_const, map_zero] at h
    exact h
  rw [probabilityLpIntegral_apply] at hint
  change (@integral ℝ 𝕜 _ (NormedSpace.restrictScalars ℝ 𝕜 𝕜)
    _ unitIntervalMeasure (fun x => f x)) = 0 at hint
  rw [NormedSpace.restrictScalars_eq] at hint
  have hcoef (n : ℕ) (k : Fin (2 ^ n)) :
      P5Support.lpHaarDyadicCoefficient 𝕜 q n k f = 0 := by
    exact (congrArg (fun L : Lp 𝕜 p unitIntervalMeasure →L[𝕜] 𝕜 => L f)
      (dyadicHaarCoordinate_eq_support (𝕜 := 𝕜) (p := p) ⟨n, k⟩)).symm.trans
      (hcoeff ⟨n, k⟩)
  have havzero (n : ℕ) : P5Support.lpHaarDyadicMean 𝕜 q hp n f = 0 := by
    rw [P5Support.lpHaarDyadicMean_eq_partialSum,
      P5Support.lpHaarDyadicMean_root]
    have hroot : P5Support.lpHaarRawCoordinate 𝕜 q none f = 0 := by
      change P5Support.lpHaarIntegral f = 0
      rw [P5Support.lpHaarIntegral_apply]
      exact hint
    rw [hroot, zero_smul, zero_add]
    apply Finset.sum_eq_zero
    intro m _
    rw [P5Support.lpHaarLevelProjection_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [hcoef, zero_smul]
  have hlim := P5Support.lpHaarDyadicMean_tendsto 𝕜 q hp f
  have hzero : Tendsto (fun n => P5Support.lpHaarDyadicMean 𝕜 q hp n f)
      atTop (𝓝 0) := by
    simp_rw [havzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hzero

theorem productHaarCoordinates_eq_zero (hp : p ≠ ∞) (f : MixedNorm 𝕜 p)
    (hf : f ∈ DoublyZeroMean 𝕜 p)
    (hcoeff : ∀ I J, productHaarCoordinate 𝕜 p I J f = 0) : f = 0 := by
  let inner (J : DyadicIndex) := dyadicHaarCoordinate 𝕜 1 J
  have hinner (J : DyadicIndex) : (inner J).compLpL p unitIntervalMeasure f = 0 := by
    apply scalarHaarCoordinates_eq_zero hp
    · have hc := congrArg (fun L : MixedNorm 𝕜 p →L[𝕜]
          Lp 𝕜 p unitIntervalMeasure => L f) (probabilityLpMean_natural (inner J))
      change probabilityLpMean (𝕜 := 𝕜) ((inner J).compLpL p unitIntervalMeasure f) =
        (inner J).compLpL p unitIntervalMeasure (outerExpectation 𝕜 p f) at hc
      rw [hc, (show outerExpectation 𝕜 p f = 0 from hf.1), map_zero]
    · intro I
      exact hcoeff I J
  have hpoint (J : DyadicIndex) : ∀ᵐ x ∂unitIntervalMeasure, inner J (f x) = 0 := by
    filter_upwards [(inner J).coeFn_compLpL f,
      Lp.coeFn_zero 𝕜 p unitIntervalMeasure] with x hc hz
    have h := congrArg (fun g : Lp 𝕜 p unitIntervalMeasure => g x) (hinner J)
    change ((inner J).compLpL p unitIntervalMeasure f) x =
      (0 : Lp 𝕜 p unitIntervalMeasure) x at h
    rw [hc, hz] at h
    exact h
  have hpointmean : ∀ᵐ x ∂unitIntervalMeasure,
      probabilityLpMean (𝕜 := 𝕜) (f x) = 0 := by
    filter_upwards [(probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (μ := unitIntervalMeasure)).coeFn_compLpL f,
      Lp.coeFn_zero (Lp 𝕜 1 unitIntervalMeasure) p unitIntervalMeasure] with x hc hz
    have h := congrArg (fun g : MixedNorm 𝕜 p => g x)
      (show innerExpectation 𝕜 p f = 0 from hf.2)
    change ((probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (μ := unitIntervalMeasure)).compLpL p unitIntervalMeasure f) x =
        (0 : MixedNorm 𝕜 p) x at h
    rw [hc, hz] at h
    exact h
  apply Lp.ext
  filter_upwards [eventually_countable_forall.mpr hpoint, hpointmean,
    Lp.coeFn_zero (Lp 𝕜 1 unitIntervalMeasure) p unitIntervalMeasure] with x hx hmean hz
  rw [hz]
  exact scalarHaarCoordinates_eq_zero (by norm_num) (f x) hmean hx

theorem productHaarCoordinates_separate (hp : p ≠ ∞) (f g : MixedNorm 𝕜 p)
    (hf : f ∈ DoublyZeroMean 𝕜 p) (hg : g ∈ DoublyZeroMean 𝕜 p)
    (hcoeff : ∀ I J, productHaarCoordinate 𝕜 p I J f =
      productHaarCoordinate 𝕜 p I J g) : f = g := by
  apply sub_eq_zero.mp
  apply productHaarCoordinates_eq_zero hp (f - g) ((DoublyZeroMean 𝕜 p).sub_mem hf hg)
  intro I J
  rw [map_sub, hcoeff I J, sub_self]

end SurveyStatements.P5
