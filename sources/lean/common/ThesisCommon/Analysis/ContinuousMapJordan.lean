import ThesisCommon.Analysis.ContinuousMapPositivePart
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-! Positive and negative bounded real functionals on a compact space.
The positive part is constructed by the Riesz--Kantorovich supremum on
the positive cone, then extended additively to the whole function space. -/
noncomputable section
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

@[simp] theorem continuousMapPositiveValue_zero (μ : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapPositiveValue μ 0 = 0 := by
  simp [continuousMapPositiveValue]

def continuousMapPositiveExtension (μ : C(K, ℝ) →L[ℝ] ℝ) (f : C(K, ℝ)) : ℝ :=
  continuousMapPositiveValue μ f⁺ - continuousMapPositiveValue μ f⁻

theorem continuousMapPositiveExtension_sub (μ : C(K, ℝ) →L[ℝ] ℝ)
    {a b : C(K, ℝ)} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    continuousMapPositiveExtension μ (a-b) =
      continuousMapPositiveValue μ a - continuousMapPositiveValue μ b := by
  have he : (a-b)⁺ + b = a + (a-b)⁻ := by
    exact sub_eq_sub_iff_add_eq_add.mp (posPart_sub_negPart (a-b))
  have h := congrArg (continuousMapPositiveValue μ) he
  rw [continuousMapPositiveValue_add μ (posPart_nonneg _) hb,
    continuousMapPositiveValue_add μ ha (negPart_nonneg _)] at h
  unfold continuousMapPositiveExtension
  linarith

theorem continuousMapPositiveExtension_add (μ : C(K, ℝ) →L[ℝ] ℝ)
    (f g : C(K, ℝ)) : continuousMapPositiveExtension μ (f+g) =
      continuousMapPositiveExtension μ f + continuousMapPositiveExtension μ g := by
  have he : f+g = (f⁺+g⁺) - (f⁻+g⁻) := by
    rw [add_sub_add_comm, posPart_sub_negPart, posPart_sub_negPart]
  rw [he, continuousMapPositiveExtension_sub μ
    (add_nonneg (posPart_nonneg _) (posPart_nonneg _))
    (add_nonneg (negPart_nonneg _) (negPart_nonneg _)),
    continuousMapPositiveValue_add μ (posPart_nonneg _) (posPart_nonneg _),
    continuousMapPositiveValue_add μ (negPart_nonneg _) (negPart_nonneg _)]
  unfold continuousMapPositiveExtension
  ring

theorem continuousMap_norm_posPart_le (f : C(K, ℝ)) : ‖f⁺‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro t
  change |max (f t) 0| ≤ ‖f‖
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self (f t)).trans (f.norm_coe_le_norm t)) (norm_nonneg f)

theorem continuousMapPositiveExtension_bound (μ : C(K, ℝ) →L[ℝ] ℝ)
    (f : C(K, ℝ)) : ‖continuousMapPositiveExtension μ f‖ ≤ ‖μ‖ * ‖f‖ := by
  have hpos := continuousMapPositiveValue_nonneg μ (posPart_nonneg f)
  have hneg := continuousMapPositiveValue_nonneg μ (negPart_nonneg f)
  have hp := (continuousMapPositiveValue_le μ (posPart_nonneg f)).trans
    (mul_le_mul_of_nonneg_left (continuousMap_norm_posPart_le f) (norm_nonneg μ))
  have hn := (continuousMapPositiveValue_le μ (negPart_nonneg f)).trans
    (mul_le_mul_of_nonneg_left (show ‖f⁻‖ ≤ ‖f‖ by
      simpa only [posPart_neg, norm_neg] using continuousMap_norm_posPart_le (-f))
      (norm_nonneg μ))
  rw [Real.norm_eq_abs, continuousMapPositiveExtension, abs_le]
  constructor <;> linarith

def continuousMapPositiveAddHom (μ : C(K, ℝ) →L[ℝ] ℝ) : C(K, ℝ) →+ ℝ where
  toFun := continuousMapPositiveExtension μ
  map_zero' := by simp [continuousMapPositiveExtension]
  map_add' := continuousMapPositiveExtension_add μ

/-- The bounded positive part of an arbitrary real bounded functional. -/
def continuousMapPositivePart (μ : C(K, ℝ) →L[ℝ] ℝ) : C(K, ℝ) →L[ℝ] ℝ :=
  (continuousMapPositiveAddHom μ).toRealLinearMap
    (AddMonoidHomClass.continuous_of_bound (continuousMapPositiveAddHom μ) ‖μ‖
      (continuousMapPositiveExtension_bound μ))

theorem continuousMapPositivePart_apply_nonneg (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) :
    continuousMapPositivePart μ f = continuousMapPositiveValue μ f := by
  change continuousMapPositiveExtension μ f = _
  simp [continuousMapPositiveExtension, posPart_of_nonneg hf, negPart_of_nonneg hf]

theorem continuousMapPositivePart_nonneg (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) : 0 ≤ continuousMapPositivePart μ f := by
  rw [continuousMapPositivePart_apply_nonneg μ hf]
  exact continuousMapPositiveValue_nonneg μ hf

theorem norm_continuousMapPositivePart_le (μ : C(K, ℝ) →L[ℝ] ℝ) :
    ‖continuousMapPositivePart μ‖ ≤ ‖μ‖ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg μ)
    (continuousMapPositiveExtension_bound μ)

/-- The positive part as a bundled positive linear map. -/
def continuousMapPositiveLinear (μ : C(K, ℝ) →L[ℝ] ℝ) : C(K, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (continuousMapPositivePart μ).toLinearMap
    (fun _ h => continuousMapPositivePart_nonneg μ h)

/-- The negative part; positivity follows from the defining supremum. -/
def continuousMapNegativePart (μ : C(K, ℝ) →L[ℝ] ℝ) : C(K, ℝ) →L[ℝ] ℝ :=
  continuousMapPositivePart μ - μ

theorem continuousMapNegativePart_nonneg (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) : 0 ≤ continuousMapNegativePart μ f := by
  change 0 ≤ continuousMapPositivePart μ f - μ f
  rw [continuousMapPositivePart_apply_nonneg μ hf]
  exact sub_nonneg.2 (le_continuousMapPositiveValue μ hf)

def continuousMapNegativeLinear (μ : C(K, ℝ) →L[ℝ] ℝ) : C(K, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (continuousMapNegativePart μ).toLinearMap
    (fun _ h => continuousMapNegativePart_nonneg μ h)

theorem continuousMap_jordan_decomposition (μ : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapPositivePart μ - continuousMapNegativePart μ = μ := by
  unfold continuousMapNegativePart
  abel

end ThesisCommon
