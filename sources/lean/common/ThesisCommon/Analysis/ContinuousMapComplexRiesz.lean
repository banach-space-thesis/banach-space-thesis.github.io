import ThesisCommon.Analysis.ContinuousMapRiesz
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-! Riesz representation over either real or complex scalars, retaining
actual finite regular measures and a quantitative dominating measure. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {K 𝕜 : Type*} [TopologicalSpace K] [CompactSpace K] [RCLike 𝕜]

def continuousMapOfReal : C(K, ℝ) →L[ℝ] C(K, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun t => (f t : 𝕜), RCLike.continuous_ofReal.comp f.continuous⟩
      map_add' := fun f g => by ext t; simp
      map_smul' := fun c f => by ext t; simp }
    1 (fun f => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro t
      change ‖(f t : 𝕜)‖ ≤ ‖f‖
      simpa only [RCLike.norm_ofReal] using f.norm_coe_le_norm t)

@[simp] theorem continuousMapOfReal_apply (f : C(K, ℝ)) (t : K) :
    continuousMapOfReal (𝕜 := 𝕜) f t = (f t : 𝕜) := rfl

theorem norm_continuousMapOfReal_apply (f : C(K, ℝ)) :
    ‖continuousMapOfReal (𝕜 := 𝕜) f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
    intro t
    simpa only [continuousMapOfReal_apply, RCLike.norm_ofReal] using f.norm_coe_le_norm t
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro t
    simpa only [continuousMapOfReal_apply, RCLike.norm_ofReal] using
      (continuousMapOfReal (𝕜 := 𝕜) f).norm_coe_le_norm t

def continuousMapRealPart (f : C(K, 𝕜)) : C(K, ℝ) :=
  ⟨fun t => RCLike.re (f t), RCLike.continuous_re.comp f.continuous⟩

def continuousMapImagPart (f : C(K, 𝕜)) : C(K, ℝ) :=
  ⟨fun t => RCLike.im (f t), RCLike.continuous_im.comp f.continuous⟩

theorem continuousMap_re_add_im (f : C(K, 𝕜)) :
    continuousMapOfReal (𝕜 := 𝕜) (continuousMapRealPart f) +
      (RCLike.I : 𝕜) • continuousMapOfReal (𝕜 := 𝕜) (continuousMapImagPart f) = f := by
  ext t
  change (RCLike.re (f t) : 𝕜) + RCLike.I * (RCLike.im (f t) : 𝕜) = f t
  rw [mul_comm, RCLike.re_add_im]

def continuousMapFunctionalRe (μ : C(K, 𝕜) →L[𝕜] 𝕜) : C(K, ℝ) →L[ℝ] ℝ :=
  RCLike.reCLM.comp ((μ.restrictScalars ℝ).comp continuousMapOfReal)

def continuousMapFunctionalIm (μ : C(K, 𝕜) →L[𝕜] 𝕜) : C(K, ℝ) →L[ℝ] ℝ :=
  RCLike.imCLM.comp ((μ.restrictScalars ℝ).comp continuousMapOfReal)

theorem norm_continuousMapFunctionalRe_le (μ : C(K, 𝕜) →L[𝕜] 𝕜) :
    ‖continuousMapFunctionalRe μ‖ ≤ ‖μ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg μ)
  intro f
  change ‖RCLike.re (μ (continuousMapOfReal f))‖ ≤ _
  exact (RCLike.norm_re_le_norm _).trans
    ((μ.le_opNorm _).trans_eq (by rw [norm_continuousMapOfReal_apply]))

theorem norm_continuousMapFunctionalIm_le (μ : C(K, 𝕜) →L[𝕜] 𝕜) :
    ‖continuousMapFunctionalIm μ‖ ≤ ‖μ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg μ)
  intro f
  change ‖RCLike.im (μ (continuousMapOfReal f))‖ ≤ _
  exact (RCLike.norm_im_le_norm _).trans
    ((μ.le_opNorm _).trans_eq (by rw [norm_continuousMapOfReal_apply]))

theorem continuousMap_functional_real_test (μ : C(K, 𝕜) →L[𝕜] 𝕜)
    (f : C(K, ℝ)) : μ (continuousMapOfReal f) =
      (continuousMapFunctionalRe μ f : 𝕜) +
        (continuousMapFunctionalIm μ f : 𝕜) * RCLike.I :=
  (RCLike.re_add_im _).symm

variable [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem continuousMap_integral_re_add_im (ν : Measure K) [IsFiniteMeasure ν]
    (f : C(K, 𝕜)) : ∫ t, f t ∂ν =
      ((∫ t, continuousMapRealPart f t ∂ν : ℝ) : 𝕜) +
        ((∫ t, continuousMapImagPart f t ∂ν : ℝ) : 𝕜) * RCLike.I := by
  exact (integral_re_add_im (f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace f))).symm

/-- The real/complex Riesz formula with four genuine finite positive regular measures. -/
theorem continuousMap_complex_riesz_representation (μ : C(K, 𝕜) →L[𝕜] 𝕜)
    (f : C(K, 𝕜)) : μ f =
      ((∫ t, f t ∂continuousMapRieszPositive (continuousMapFunctionalRe μ)) -
        (∫ t, f t ∂continuousMapRieszNegative (continuousMapFunctionalRe μ))) +
      (((∫ t, f t ∂continuousMapRieszPositive (continuousMapFunctionalIm μ)) -
        (∫ t, f t ∂continuousMapRieszNegative (continuousMapFunctionalIm μ)))) * RCLike.I := by
  have hf := congrArg μ (continuousMap_re_add_im f)
  rw [map_add, map_smul, smul_eq_mul,
    continuousMap_functional_real_test, continuousMap_functional_real_test] at hf
  rw [← hf]
  simp_rw [continuousMap_integral_re_add_im _ f]
  rw [continuousMap_real_riesz_representation (continuousMapFunctionalRe μ) (continuousMapRealPart f),
    continuousMap_real_riesz_representation (continuousMapFunctionalIm μ) (continuousMapRealPart f),
    continuousMap_real_riesz_representation (continuousMapFunctionalRe μ) (continuousMapImagPart f),
    continuousMap_real_riesz_representation (continuousMapFunctionalIm μ) (continuousMapImagPart f)]
  simp only [RCLike.ofReal_sub]
  ring

/-- An explicit positive measure dominating the four scalar measure components. -/
def continuousMapRieszControl (μ : C(K, 𝕜) →L[𝕜] 𝕜) : Measure K :=
  (continuousMapRieszPositive (continuousMapFunctionalRe μ) +
    continuousMapRieszNegative (continuousMapFunctionalRe μ)) +
    (continuousMapRieszPositive (continuousMapFunctionalIm μ) +
    continuousMapRieszNegative (continuousMapFunctionalIm μ))

instance continuousMapRieszControl_finite (μ : C(K, 𝕜) →L[𝕜] 𝕜) :
    IsFiniteMeasure (continuousMapRieszControl μ) := by
  unfold continuousMapRieszControl
  infer_instance

theorem continuousMapRieszControl_mass_le (μ : C(K, 𝕜) →L[𝕜] 𝕜) :
    (continuousMapRieszControl μ).real Set.univ ≤ 2 * ‖μ‖ := by
  unfold continuousMapRieszControl
  rw [measureReal_add_apply, measureReal_add_apply, measureReal_add_apply,
    continuousMapRiesz_total_mass]
  rw [continuousMapRiesz_total_mass]
  have hr := norm_continuousMapFunctionalRe_le μ
  have hi := norm_continuousMapFunctionalIm_le μ
  linarith

/-- The representing vector measure; for complex scalars this is a `ComplexMeasure`. -/
def continuousMapRieszVector (μ : C(K, 𝕜) →L[𝕜] 𝕜) : VectorMeasure K 𝕜 :=
  (continuousMapRieszSigned (continuousMapFunctionalRe μ)).mapRange
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).toAddMonoidHom RCLike.ofRealCLM.continuous +
    (RCLike.I : 𝕜) • (continuousMapRieszSigned (continuousMapFunctionalIm μ)).mapRange
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).toAddMonoidHom RCLike.ofRealCLM.continuous

theorem continuousMapRieszVector_apply (μ : C(K, 𝕜) →L[𝕜] 𝕜)
    (s : Set K) : continuousMapRieszVector μ s =
      (continuousMapRieszSigned (continuousMapFunctionalRe μ) s : 𝕜) +
        (continuousMapRieszSigned (continuousMapFunctionalIm μ) s : 𝕜) * RCLike.I := by
  simp [continuousMapRieszVector, VectorMeasure.mapRange_apply, mul_comm]

end ThesisCommon
