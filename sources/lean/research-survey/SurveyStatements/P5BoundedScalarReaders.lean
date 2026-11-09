import SurveyStatements.P5RademacherPointwise

/-! Pointwise bounded real multiplication and its integration reader on
actual Lp. The Rademacher functions satisfy these hypotheses pointwise. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem boundedMultiply_memLp (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp ℝ p unitIntervalMeasure) :
    MemLp (fun x => η x * f x) p unitIntervalMeasure := by
  apply (Lp.memLp f).of_le (hη.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  apply Eventually.of_forall
  intro x
  change ‖η x * f x‖ ≤ ‖f x‖
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x))).trans_eq (one_mul _)

def boundedMultiplyValue (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp ℝ p unitIntervalMeasure) :
    Lp ℝ p unitIntervalMeasure :=
  (boundedMultiply_memLp η hη hb f).toLp (fun x => η x * f x)

theorem boundedMultiplyValue_ae (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp ℝ p unitIntervalMeasure) :
    boundedMultiplyValue η hη hb f =ᵐ[unitIntervalMeasure] fun x => η x * f x :=
  MemLp.coeFn_toLp _

theorem norm_boundedMultiplyValue_le (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp ℝ p unitIntervalMeasure) :
    ‖boundedMultiplyValue η hη hb f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [boundedMultiplyValue_ae η hη hb f] with x hx
  rw [hx, norm_mul]
  exact (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x))).trans_eq (one_mul _)

def boundedMultiply (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : Lp ℝ p unitIntervalMeasure →L[ℝ] Lp ℝ p unitIntervalMeasure :=
  LinearMap.mkContinuous
    { toFun := boundedMultiplyValue η hη hb
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [boundedMultiplyValue_ae η hη hb (f + g),
          boundedMultiplyValue_ae η hη hb f, boundedMultiplyValue_ae η hη hb g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (boundedMultiplyValue η hη hb f) (boundedMultiplyValue η hη hb g)]
          with x h₁ h₂ h₃ h₄ h₅
        simp only [Pi.add_apply] at h₄ h₅
        rw [h₁, h₄, h₅, h₂, h₃, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [boundedMultiplyValue_ae η hη hb (c • f),
          boundedMultiplyValue_ae η hη hb f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (boundedMultiplyValue η hη hb f)] with x h₁ h₂ h₃ h₄
        simp only [Pi.smul_apply, smul_eq_mul] at h₃ h₄
        simp only [RingHom.id_apply]
        rw [h₁, h₃, h₄, h₂]
        ring }
    1 (fun f => by simpa only [one_mul] using norm_boundedMultiplyValue_le η hη hb f)

theorem norm_boundedMultiply_le (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : ‖boundedMultiply (p := p) η hη hb‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def boundedScalarReader (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : Lp ℝ p unitIntervalMeasure →L[ℝ] ℝ :=
  (probabilityLpIntegral (𝕜 := ℝ)).comp (boundedMultiply η hη hb)

theorem boundedScalarReader_apply (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp ℝ p unitIntervalMeasure) :
    boundedScalarReader η hη hb f = ∫ x, η x * f x ∂unitIntervalMeasure := by
  change probabilityLpIntegral (𝕜 := ℝ) (boundedMultiplyValue η hη hb f) = _
  rw [probabilityLpIntegral_apply]
  change (@integral ℝ ℝ _ (NormedSpace.restrictScalars ℝ ℝ ℝ) _ unitIntervalMeasure
    (fun x => boundedMultiplyValue η hη hb f x)) = _
  rw [NormedSpace.restrictScalars_eq]
  exact integral_congr_ae (boundedMultiplyValue_ae η hη hb f)

theorem norm_boundedScalarReader_le (η : ℝ → ℝ) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : ‖boundedScalarReader (p := p) η hη hb‖ ≤ 1 := by
  calc
    _ ≤ ‖probabilityLpIntegral (𝕜 := ℝ) (E := ℝ) (p := p)
        (μ := unitIntervalMeasure)‖ * ‖boundedMultiply (p := p) η hη hb‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul norm_probabilityLpIntegral_le (norm_boundedMultiply_le η hη hb)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end SurveyStatements.P5
