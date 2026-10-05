import ThesisCommon.Analysis.LpHaarCoefficient

/-! Sharp finite-measure integration estimates and averaging projections.
These estimates supply the uniform bounds needed for dyadic averaging. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

theorem lpHaarFiniteIntegral_norm_le (hp : p ≠ ∞) (f : Lp 𝕜 p μ) :
    ‖∫ x, f x ∂μ‖ ≤ μ.real univ ^ (1 - 1 / p.toReal) * ‖f‖ := by
  have hpR : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  have he : 0 ≤ 1 - 1 / p.toReal := by
    have h := (div_le_one (by linarith : 0 < p.toReal)).mpr hpR
    linarith
  refine (norm_integral_le_lintegral_norm f).trans ?_
  simp only [ofReal_norm_eq_enorm, ← eLpNorm_one_eq_lintegral_enorm]
  calc
    (eLpNorm f 1 μ).toReal ≤
        (eLpNorm f p μ * μ univ ^ (1 - 1 / p.toReal)).toReal := by
      apply ENNReal.toReal_mono
      · exact ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
          (ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ univ))
      · simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (show 1 ≤ p from Fact.out) (Lp.memLp f).1
    _ = _ := by rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]; exact mul_comm _ _

def lpHaarFiniteIntegral (hp : p ≠ ∞) : Lp 𝕜 p μ →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => by
        rw [integral_congr_ae (Lp.coeFn_add f g)]
        exact integral_add ((Lp.memLp f).integrable Fact.out)
          ((Lp.memLp g).integrable Fact.out)
      map_smul' := fun c f => by
        rw [integral_congr_ae (Lp.coeFn_smul c f)]
        exact integral_smul c f }
    (μ.real univ ^ (1 - 1 / p.toReal)) (lpHaarFiniteIntegral_norm_le hp)

@[simp] theorem lpHaarFiniteIntegral_apply (hp : p ≠ ∞) (f : Lp 𝕜 p μ) :
    lpHaarFiniteIntegral hp f = ∫ x, f x ∂μ := rfl

theorem norm_lpHaarFiniteIntegral_le (hp : p ≠ ∞) :
    ‖lpHaarFiniteIntegral (𝕜 := 𝕜) (μ := μ) hp‖ ≤ μ.real univ ^ (1 - 1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

def lpHaarMean (hp : p ≠ ∞) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  (Lp.constL p μ 𝕜).comp ((μ.real univ : 𝕜)⁻¹ • lpHaarFiniteIntegral hp)

theorem lpHaarMean_apply (hp : p ≠ ∞) (f : Lp 𝕜 p μ) :
    lpHaarMean hp f = Lp.const p μ ((μ.real univ : 𝕜)⁻¹ * ∫ x, f x ∂μ) := rfl

theorem lpHaarMean_norm_le (hp : p ≠ ∞) (hμ : μ univ ≠ 0) (f : Lp 𝕜 p μ) :
    ‖lpHaarMean hp f‖ ≤ ‖f‖ := by
  have hm : 0 < μ.real univ := ENNReal.toReal_pos hμ (measure_ne_top μ univ)
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  rw [lpHaarMean_apply, Lp.norm_const' _ _ _ hp0 hp,
    norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hm]
  calc
    (μ.real univ)⁻¹ * ‖∫ x, f x ∂μ‖ * μ.real univ ^ (1 / p.toReal) ≤
        (μ.real univ)⁻¹ * (μ.real univ ^ (1 - 1 / p.toReal) * ‖f‖) *
          μ.real univ ^ (1 / p.toReal) := by
      gcongr
      exact lpHaarFiniteIntegral_norm_le hp f
    _ = ((μ.real univ)⁻¹ *
        (μ.real univ ^ (1 - 1 / p.toReal) * μ.real univ ^ (1 / p.toReal))) * ‖f‖ := by ring
    _ = ‖f‖ := by
      rw [← Real.rpow_add hm]
      simp [hm.ne']

theorem norm_lpHaarMean_le (hp : p ≠ ∞) (hμ : μ univ ≠ 0) :
    ‖lpHaarMean (𝕜 := 𝕜) (μ := μ) hp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using lpHaarMean_norm_le hp hμ f

theorem lpHaarMean_const (hp : p ≠ ∞) (hμ : μ univ ≠ 0) (c : 𝕜) :
    lpHaarMean hp (Lp.const p μ c) = Lp.const p μ c := by
  rw [lpHaarMean_apply, integral_congr_ae (Lp.coeFn_const p μ c)]
  simp only [Function.const_apply, integral_const]
  have hm : (μ.real univ : 𝕜) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hμ, measure_ne_top μ univ⟩)
  simp only [Algebra.smul_def, RCLike.algebraMap_eq_ofReal]
  rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

theorem lpHaarMean_idempotent (hp : p ≠ ∞) (hμ : μ univ ≠ 0) :
    (lpHaarMean (𝕜 := 𝕜) (μ := μ) hp).comp (lpHaarMean hp) = lpHaarMean hp := by
  apply ContinuousLinearMap.ext
  intro f
  change lpHaarMean hp (lpHaarMean hp f) = lpHaarMean hp f
  rw [lpHaarMean_apply hp f, lpHaarMean_const hp hμ]

end ThesisCommon
