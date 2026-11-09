import SurveyStatements.P5Definitions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.NormNum

/-! Actual bounded Bochner integration and averaging on the probability spaces
used by Problem 5, including vector-valued Lp functions. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal

namespace SurveyStatements.P5

instance unitIntervalMeasure_probability : IsProbabilityMeasure unitIntervalMeasure :=
  ⟨by simp [unitIntervalMeasure]⟩

variable {𝕜 α E F : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsProbabilityMeasure μ]

local instance : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
local instance : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance : Module ℝ F := RestrictScalars.module ℝ 𝕜 F
local instance : IsScalarTower ℝ 𝕜 F := RestrictScalars.isScalarTower ℝ 𝕜 F
local instance : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F

theorem norm_integral_le_lp_norm (f : Lp E p μ) : ‖∫ x, f x ∂μ‖ ≤ ‖f‖ := by
  refine (norm_integral_le_lintegral_norm f).trans ?_
  simp only [ofReal_norm_eq_enorm, ← eLpNorm_one_eq_lintegral_enorm]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le Fact.out (Lp.memLp f).1)

/-- Bochner integration is a contraction from Lp on a probability space. -/
def probabilityLpIntegral : Lp E p μ →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => by
        rw [integral_congr_ae (Lp.coeFn_add f g)]
        exact integral_add ((Lp.memLp f).integrable Fact.out)
          ((Lp.memLp g).integrable Fact.out)
      map_smul' := fun c f => by
        rw [integral_congr_ae (Lp.coeFn_smul c f)]
        exact integral_smul c f }
    1 (fun f => by simpa only [one_mul] using norm_integral_le_lp_norm f)

@[simp] theorem probabilityLpIntegral_apply (f : Lp E p μ) :
    probabilityLpIntegral (𝕜 := 𝕜) f = ∫ x, f x ∂μ := rfl

theorem norm_probabilityLpIntegral_le :
    ‖probabilityLpIntegral (𝕜 := 𝕜) (E := E) (p := p) (μ := μ)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem probabilityLpIntegral_const (c : E) :
    probabilityLpIntegral (𝕜 := 𝕜) (Lp.const p μ c) = c := by
  rw [probabilityLpIntegral_apply, integral_congr_ae (Lp.coeFn_const p μ c)]
  simp

/-- The integral of a constant indicator, stated using the given scalar field.
This avoids exposing an auxiliary restricted-real-space instance to callers. -/
theorem probabilityLpIntegral_indicator (s : Set α) (hs : MeasurableSet s) (c : E) :
    probabilityLpIntegral (𝕜 := 𝕜)
      (indicatorConstLp p hs (measure_ne_top μ s) c) = (μ.real s : 𝕜) • c := by
  rw [probabilityLpIntegral_apply, integral_indicatorConstLp,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)]

theorem norm_probabilityLpConst_le :
    ‖(Lp.constL p μ 𝕜 : E →L[𝕜] Lp E p μ)‖ ≤ 1 := by
  simpa using Lp.norm_constL_le (E := E) p μ 𝕜

/-- Averaging: replace an Lp function by the constant equal to its integral. -/
def probabilityLpMean : Lp E p μ →L[𝕜] Lp E p μ :=
  (Lp.constL p μ 𝕜).comp probabilityLpIntegral

@[simp] theorem probabilityLpMean_apply (f : Lp E p μ) :
    probabilityLpMean (𝕜 := 𝕜) f =
      Lp.const p μ (probabilityLpIntegral (𝕜 := 𝕜) f) := rfl

theorem norm_probabilityLpMean_le :
    ‖probabilityLpMean (𝕜 := 𝕜) (E := E) (p := p) (μ := μ)‖ ≤ 1 := by
  calc
    _ ≤ ‖(Lp.constL p μ 𝕜 : E →L[𝕜] Lp E p μ)‖ * ‖probabilityLpIntegral‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 :=
      mul_le_mul norm_probabilityLpConst_le norm_probabilityLpIntegral_le
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

@[simp] theorem probabilityLpMean_const (c : E) :
    probabilityLpMean (𝕜 := 𝕜) (Lp.const p μ c) = Lp.const p μ c := by
  rw [probabilityLpMean_apply, probabilityLpIntegral_const]

theorem probabilityLpMean_idempotent :
    (probabilityLpMean (𝕜 := 𝕜) (E := E) (p := p) (μ := μ)).comp
        probabilityLpMean = probabilityLpMean := by
  apply ContinuousLinearMap.ext
  intro f
  change probabilityLpMean (𝕜 := 𝕜) (probabilityLpMean (𝕜 := 𝕜) f) =
    probabilityLpMean (𝕜 := 𝕜) f
  rw [probabilityLpMean_apply (𝕜 := 𝕜) f, probabilityLpMean_const]

theorem compLpL_const (L : E →L[𝕜] F) (c : E) :
    L.compLpL p μ (Lp.const p μ c) = Lp.const p μ (L c) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (Lp.const p μ c), Lp.coeFn_const p μ c,
    Lp.coeFn_const p μ (L c)] with x hL hc hLc
  rw [hL, hc, hLc]
  rfl

/-- Bounded linear maps commute with averaging. This supplies commutativity
of the two coordinate expectations in the mixed-norm space. -/
theorem probabilityLpMean_natural (L : E →L[𝕜] F) :
    (probabilityLpMean (𝕜 := 𝕜) (E := F) (p := p) (μ := μ)).comp (L.compLpL p μ) =
      (L.compLpL p μ).comp probabilityLpMean := by
  apply ContinuousLinearMap.ext
  intro f
  change Lp.const p μ (probabilityLpIntegral (𝕜 := 𝕜) (L.compLpL p μ f)) =
    L.compLpL p μ (Lp.const p μ (probabilityLpIntegral (𝕜 := 𝕜) f))
  rw [compLpL_const]
  congr 1
  rw [probabilityLpIntegral_apply, probabilityLpIntegral_apply,
    integral_congr_ae (L.coeFn_compLpL f)]
  exact L.integral_comp_comm ((Lp.memLp f).integrable Fact.out)

/-- Pointwise lifting preserves projection identities. -/
theorem compLpL_idempotent (L : E →L[𝕜] E) (hL : L.comp L = L) :
    (L.compLpL p μ).comp (L.compLpL p μ) = L.compLpL p μ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (L.compLpL p μ f), L.coeFn_compLpL f]
    with x houter hinner
  change (L.compLpL p μ (L.compLpL p μ f)) x = (L.compLpL p μ f) x
  rw [houter, hinner]
  exact congrArg (fun A : E →L[𝕜] E => A (f x)) hL

end SurveyStatements.P5
