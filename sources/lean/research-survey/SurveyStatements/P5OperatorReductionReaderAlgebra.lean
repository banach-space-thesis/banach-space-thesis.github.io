import SurveyStatements.P5OperatorReductionPairing

/-! Actual integral and finite-sum formulas for bounded outer readers. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
local instance : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

theorem weightedOuterReader_apply (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp E p unitIntervalMeasure) :
    weightedOuterReader η hη hb f = ∫ x, η x • f x ∂unitIntervalMeasure := by
  change probabilityLpIntegral (𝕜 := 𝕜) (vectorBoundedMultiply η hη hb f) = _
  rw [probabilityLpIntegral_apply]
  exact integral_congr_ae (vectorBoundedMultiplyValue_ae η hη hb f)

theorem weightedOuterReader_finite_sum {ι : Type*} (F : Finset ι)
    (η : ι → ℝ → 𝕜) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1)
    (ξ : ℝ → 𝕜) (hξ : StronglyMeasurable ξ) (hξb : ∀ x, ‖ξ x‖ ≤ 1)
    (heq : ∀ x, ξ x = ∑ i ∈ F, η i x) (f : Lp E p unitIntervalMeasure) :
    weightedOuterReader ξ hξ hξb f = ∑ i ∈ F,
      weightedOuterReader (η i) (hη i) (hb i) f := by
  simp_rw [weightedOuterReader_apply, heq, Finset.sum_smul]
  exact integral_finset_sum _ (fun i _ =>
    (vectorBoundedMultiply_memLp (η i) (hη i) (hb i) f).integrable Fact.out)

theorem weightedOuterReader_signed_sum {n : ℕ}
    (η : Fin n → ℝ → 𝕜) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) (θ : Fin n → Bool)
    (ξ : ℝ → 𝕜) (hξ : StronglyMeasurable ξ) (hξb : ∀ x, ‖ξ x‖ ≤ 1)
    (heq : ∀ x, ξ x = ∑ i, signedValue (θ i) (η i x)) :
    weightedOuterReader (E := E) (p := p) ξ hξ hξb =
      ∑ i, signedValue (θ i) (weightedOuterReader (E := E) (p := p) (η i) (hη i) (hb i)) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [weightedOuterReader_finite_sum Finset.univ
    (fun i => signedWeight (θ i) (η i))
    (fun i => signedWeight_measurable (θ i) (η i) (hη i))
    (fun i => signedWeight_bound (θ i) (η i) (hb i)) ξ hξ hξb heq f]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedOuterReader_signed_param (E := E) (p := p)
    (θ i) (η i) (hη i) (hb i) f]
  cases θ i <;> simp [signedValue]

theorem vectorMean_signed_reader_input {Ω F : Type*} [Fintype Ω] [DecidableEq Ω]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : Ω → E →L[𝕜] F) (x : Ω → E) :
    vectorMean (𝕜 := 𝕜) (fun θ : Ω → Bool =>
      (∑ i, signedValue (θ i) (A i)) (∑ j, signedValue (θ j) (x j))) =
        ∑ i, A i (x i) := by
  have hcR : (Fintype.card (Ω → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card (Ω → Bool) : 𝕜) ≠ 0 := by
    simpa only [RCLike.ofReal_natCast] using RCLike.ofReal_ne_zero.mpr hcR
  rw [vectorMean, signed_reader_input_sum, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
  simp only [RCLike.ofReal_inv, RCLike.ofReal_natCast, inv_mul_cancel₀ hc, one_smul]

end SurveyStatements.P5OperatorReduction
