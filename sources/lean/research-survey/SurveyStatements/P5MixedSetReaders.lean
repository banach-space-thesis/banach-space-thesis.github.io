import SurveyStatements.P5L1SetReaders
import SurveyStatements.P5BoundedScalarReaders

/-! Disjoint inner set readers paired with pointwise bounded outer scalar
functions form a norm-one reader on the actual mixed Bochner space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean

def mixedSetReader {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (η : ι → ℝ → ℝ) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) : MixedNorm ℝ p →L[ℝ] ℝ :=
  ∑ i ∈ F, (boundedScalarReader (η i) (hη i) (hb i)).comp
    ((l1SetReader (S i)).compLpL p unitIntervalMeasure)

def mixedSetReaderVector {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (η : ι → ℝ → ℝ) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) (f : MixedNorm ℝ p) : Lp ℝ p unitIntervalMeasure :=
  ∑ i ∈ F, boundedMultiply (p := p) (η i) (hη i) (hb i)
    ((l1SetReader (S i)).compLpL p unitIntervalMeasure f)

theorem mixedSetReaderVector_ae {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (η : ι → ℝ → ℝ) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) (f : MixedNorm ℝ p) :
    mixedSetReaderVector F S η hη hb f =ᵐ[unitIntervalMeasure]
      fun x => ∑ i ∈ F, η i x * l1SetReader (S i) (f x) := by
  let g (i : ι) : Lp ℝ p unitIntervalMeasure :=
    boundedMultiply (p := p) (η i) (hη i) (hb i)
      ((l1SetReader (S i)).compLpL p unitIntervalMeasure f)
  have hg (i : ι) : g i =ᵐ[unitIntervalMeasure]
      fun x => η i x * l1SetReader (S i) (f x) := by
    filter_upwards [boundedMultiplyValue_ae (p := p) (η i) (hη i) (hb i)
      ((l1SetReader (S i)).compLpL p unitIntervalMeasure f),
      (l1SetReader (S i)).coeFn_compLpL f] with x h₁ h₂
    change g i x = _ at h₁
    rw [h₁, h₂]
  filter_upwards [scalarLp_sum_ae F g,
    (F.eventually_all).mpr (fun i _ => hg i)] with x hsum hterm
  change (mixedSetReaderVector F S η hη hb f) x = _ at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hterm i hi

theorem norm_mixedSetReaderVector_le {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (η : ι → ℝ → ℝ) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) (f : MixedNorm ℝ p) :
    ‖mixedSetReaderVector F S η hη hb f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [mixedSetReaderVector_ae F S η hη hb f] with x hx
  rw [hx]
  calc
    _ ≤ ∑ i ∈ F, ‖η i x * l1SetReader (S i) (f x)‖ := norm_sum_le _ _
    _ = ∑ i ∈ F, ‖η i x‖ * ‖l1SetReader (S i) (f x)‖ := by simp only [norm_mul]
    _ ≤ ∑ i ∈ F, ‖l1SetReader (S i) (f x)‖ :=
      Finset.sum_le_sum (fun i _ => by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb i x) (norm_nonneg _))
    _ ≤ ‖f x‖ := sum_norm_l1SetReader_le F S hS hdisjoint (f x)

theorem mixedSetReader_apply_vector {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (η : ι → ℝ → ℝ) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) (f : MixedNorm ℝ p) :
    mixedSetReader (p := p) F S η hη hb f =
      probabilityLpIntegral (𝕜 := ℝ) (E := ℝ) (p := p) (μ := unitIntervalMeasure)
        (mixedSetReaderVector F S η hη hb f) := by
  simp only [mixedSetReader, mixedSetReaderVector, ContinuousLinearMap.sum_apply,
    map_sum, ContinuousLinearMap.comp_apply, boundedScalarReader]

theorem norm_mixedSetReader_le {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (η : ι → ℝ → ℝ) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) :
    ‖mixedSetReader (p := p) F S η hη hb‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
    (mixedSetReader (p := p) F S η hη hb) zero_le_one
  intro f
  rw [mixedSetReader_apply_vector, one_mul]
  exact ((probabilityLpIntegral (𝕜 := ℝ) (E := ℝ) (p := p)
    (μ := unitIntervalMeasure)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right norm_probabilityLpIntegral_le (norm_nonneg _)).trans
      (by simpa only [one_mul] using norm_mixedSetReaderVector_le F S hS hdisjoint η hη hb f))

theorem mixedSetReader_tensor {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (η : ι → ℝ → ℝ) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1)
    (g : Lp ℝ 1 unitIntervalMeasure) (f : Lp ℝ p unitIntervalMeasure) :
    mixedSetReader F S η hη hb (tensorWith g f) =
      ∑ i ∈ F, l1SetReader (S i) g * boundedScalarReader (η i) (hη i) (hb i) f := by
  simp only [mixedSetReader, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    innerFunctional_tensor, map_smul, smul_eq_mul]

end SurveyStatements.P5
