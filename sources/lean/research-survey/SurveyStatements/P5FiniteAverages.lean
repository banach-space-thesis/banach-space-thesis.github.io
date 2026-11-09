import SurveyStatements.P5Averages
import SurveyStatements.P5Support.LpHaarFiniteIntegral

/-! Finite-measure Bochner integration and contractive vector-valued means.
The scalar proof in P5Support.LpHaarFiniteIntegral is extended to arbitrary
Banach-valued functions, as needed by exterior mixed-space maps. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

local instance finiteAvgModuleReal : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
local instance finiteAvgScalarTowerReal : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
local instance finiteAvgNormedSpaceReal : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

theorem norm_finiteLpIntegral_le (hp : p ≠ ∞) (f : Lp E p μ) :
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
    _ = _ := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
      exact mul_comm _ _

def finiteLpIntegral (hp : p ≠ ∞) : Lp E p μ →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => by
        rw [integral_congr_ae (Lp.coeFn_add f g)]
        exact integral_add ((Lp.memLp f).integrable Fact.out)
          ((Lp.memLp g).integrable Fact.out)
      map_smul' := fun c f => by
        rw [integral_congr_ae (Lp.coeFn_smul c f)]
        exact integral_smul c f }
    (μ.real univ ^ (1 - 1 / p.toReal)) (norm_finiteLpIntegral_le hp)

@[simp] theorem finiteLpIntegral_apply (hp : p ≠ ∞) (f : Lp E p μ) :
    finiteLpIntegral (𝕜 := 𝕜) hp f = ∫ x, f x ∂μ := rfl

theorem norm_finiteLpIntegral_le_bound (hp : p ≠ ∞) :
    ‖finiteLpIntegral (𝕜 := 𝕜) (E := E) (μ := μ) hp‖ ≤
      μ.real univ ^ (1 - 1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

def finiteLpMean (hp : p ≠ ∞) : Lp E p μ →L[𝕜] Lp E p μ :=
  (Lp.constL p μ 𝕜).comp ((μ.real univ : 𝕜)⁻¹ • finiteLpIntegral hp)

@[simp] theorem finiteLpMean_apply (hp : p ≠ ∞) (f : Lp E p μ) :
    finiteLpMean (𝕜 := 𝕜) hp f =
      Lp.const p μ ((μ.real univ : 𝕜)⁻¹ • finiteLpIntegral (𝕜 := 𝕜) hp f) := rfl

theorem finiteLpMean_norm_le (hp : p ≠ ∞) (hμ : μ univ ≠ 0) (f : Lp E p μ) :
    ‖finiteLpMean (𝕜 := 𝕜) hp f‖ ≤ ‖f‖ := by
  have hm : 0 < μ.real univ := ENNReal.toReal_pos hμ (measure_ne_top μ univ)
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  rw [finiteLpMean_apply, Lp.norm_const' _ _ _ hp0 hp,
    norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hm]
  calc
    (μ.real univ)⁻¹ * ‖finiteLpIntegral (𝕜 := 𝕜) hp f‖ * μ.real univ ^ (1 / p.toReal) ≤
        (μ.real univ)⁻¹ * (μ.real univ ^ (1 - 1 / p.toReal) * ‖f‖) *
          μ.real univ ^ (1 / p.toReal) := by
      gcongr
      exact norm_finiteLpIntegral_le hp f
    _ = ((μ.real univ)⁻¹ *
        (μ.real univ ^ (1 - 1 / p.toReal) * μ.real univ ^ (1 / p.toReal))) * ‖f‖ := by ring
    _ = ‖f‖ := by
      rw [← Real.rpow_add hm]
      simp [hm.ne']

theorem norm_finiteLpMean_le (hp : p ≠ ∞) (hμ : μ univ ≠ 0) :
    ‖finiteLpMean (𝕜 := 𝕜) (E := E) (μ := μ) hp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using finiteLpMean_norm_le hp hμ f

theorem finiteLpMean_const (hp : p ≠ ∞) (hμ : μ univ ≠ 0) (c : E) :
    finiteLpMean (𝕜 := 𝕜) hp (Lp.const p μ c) = Lp.const p μ c := by
  rw [finiteLpMean_apply, finiteLpIntegral_apply,
    integral_congr_ae (Lp.coeFn_const p μ c)]
  simp only [Function.const_apply, integral_const]
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul]
  have hm : (μ.real univ : 𝕜) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hμ, measure_ne_top μ univ⟩)
  rw [inv_mul_cancel₀ hm, one_smul]

theorem finiteLpMean_idempotent (hp : p ≠ ∞) (hμ : μ univ ≠ 0) :
    (finiteLpMean (𝕜 := 𝕜) (E := E) (μ := μ) hp).comp (finiteLpMean hp) =
      finiteLpMean hp := by
  apply ContinuousLinearMap.ext
  intro f
  change finiteLpMean (𝕜 := 𝕜) hp (finiteLpMean (𝕜 := 𝕜) hp f) =
    finiteLpMean (𝕜 := 𝕜) hp f
  rw [finiteLpMean_apply hp f, finiteLpMean_const hp hμ]

end SurveyStatements.P5
