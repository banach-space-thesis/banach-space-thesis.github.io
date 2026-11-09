import SurveyStatements.P5OperatorReductionJointReaders
import SurveyStatements.P5OperatorReductionSignIdentity

/-! Actual signed outer readers and their joint norm bound. This is the
reader side of the shadow randomization contradiction. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def signedWeight (b : Bool) (η : ℝ → 𝕜) : ℝ → 𝕜 := fun x => signedValue b (η x)

theorem signedWeight_measurable (b : Bool) (η : ℝ → 𝕜) (hη : StronglyMeasurable η) :
    StronglyMeasurable (signedWeight b η) := by
  cases b with
  | false => simpa [signedWeight, signedValue] using hη.neg
  | true => simpa [signedWeight, signedValue] using hη

theorem signedWeight_bound (b : Bool) (η : ℝ → 𝕜) (hb : ∀ x, ‖η x‖ ≤ 1) :
    ∀ x, ‖signedWeight b η x‖ ≤ 1 := by
  intro x
  simpa only [signedWeight, norm_signedValue] using hb x

theorem weightedOuterReader_signed_param
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : Bool) (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (f : Lp E p unitIntervalMeasure) :
    weightedOuterReader (signedWeight b η) (signedWeight_measurable b η hη)
      (signedWeight_bound b η hb) f = signedValue b (weightedOuterReader η hη hb f) := by
  cases b with
  | true => rfl
  | false =>
    have hmul : vectorBoundedMultiply (signedWeight false η)
        (signedWeight_measurable false η hη) (signedWeight_bound false η hb) f =
        -(vectorBoundedMultiply η hη hb f) := by
      apply Lp.ext
      filter_upwards [vectorBoundedMultiplyValue_ae (signedWeight false η)
        (signedWeight_measurable false η hη) (signedWeight_bound false η hb) f,
        vectorBoundedMultiplyValue_ae η hη hb f,
        Lp.coeFn_neg (vectorBoundedMultiply η hη hb f)] with x h₁ h₂ h₃
      change (vectorBoundedMultiply (signedWeight false η)
        (signedWeight_measurable false η hη) (signedWeight_bound false η hb) f) x =
        signedWeight false η x • f x at h₁
      change (vectorBoundedMultiply η hη hb f) x = η x • f x at h₂
      simp only [Pi.neg_apply] at h₃
      change (vectorBoundedMultiply (signedWeight false η)
        (signedWeight_measurable false η hη) (signedWeight_bound false η hb) f) x = _
      rw [h₁, h₃, h₂]
      simp [signedWeight, signedValue, neg_smul]
    change probabilityLpIntegral (𝕜 := 𝕜)
      (vectorBoundedMultiply (signedWeight false η)
        (signedWeight_measurable false η hη) (signedWeight_bound false η hb) f) =
        -(probabilityLpIntegral (𝕜 := 𝕜) (vectorBoundedMultiply η hη hb f))
    rw [hmul, map_neg]

theorem norm_signed_reader_sum_le {n : ℕ}
    (π : Fin n → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜)
    (hπ : ∀ y, ∑ i, ‖π i y‖ ≤ ‖y‖)
    (η : Fin n → ℝ → 𝕜) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) (θ : Fin n → Bool) :
    ‖∑ i, signedValue (θ i)
      ((π i).comp (weightedOuterReader (p := p) (η i) (hη i) (hb i)))‖ ≤ 1 := by
  let ηθ (i : Fin n) := signedWeight (θ i) (η i)
  have hm (i : Fin n) := signedWeight_measurable (θ i) (η i) (hη i)
  have hn (i : Fin n) := signedWeight_bound (θ i) (η i) (hb i)
  have heq : (∑ i, signedValue (θ i)
      ((π i).comp (weightedOuterReader (p := p) (η i) (hη i) (hb i)))) =
      jointWeightedReader Finset.univ π ηθ hm hn := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [ContinuousLinearMap.sum_apply, jointWeightedReader]
    apply Finset.sum_congr rfl
    intro i _
    have hnat := weightedOuterReader_natural (ηθ i) (hm i) (hn i) (π i) f
    change signedValue (θ i) ((π i).comp (weightedOuterReader (η i) (hη i) (hb i))) f =
      weightedOuterReader (ηθ i) (hm i) (hn i) ((π i).compLpL p unitIntervalMeasure f)
    rw [hnat]
    rw [weightedOuterReader_signed_param (θ i) (η i) (hη i) (hb i) f, map_signedValue]
    cases θ i <;> simp [signedValue]
  rw [heq]
  exact norm_jointWeightedReader_le Finset.univ π (by simpa using hπ) ηθ hm hn

end SurveyStatements.P5OperatorReduction
