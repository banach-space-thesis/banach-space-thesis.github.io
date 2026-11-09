import SurveyStatements.P5OperatorReductionReaders
import SurveyStatements.P5Support.LpHaarLevelVariation

/-! A simultaneous reader from actual vector-valued Lp. The variation
bound on its inner functionals is the precise property supplied by
norm-one functionals restricted to pairwise disjoint measurable sets. -/

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

attribute [local irreducible] probabilityLpIntegral probabilityLpMean

def jointWeightedReader {ι : Type*} (F : Finset ι) (π : ι → E →L[𝕜] 𝕜)
    (η : ι → ℝ → 𝕜) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) : Lp E p unitIntervalMeasure →L[𝕜] 𝕜 :=
  ∑ i ∈ F, (weightedOuterReader (η i) (hη i) (hb i)).comp
    ((π i).compLpL p unitIntervalMeasure)

def jointWeightedReaderVector {ι : Type*} (F : Finset ι) (π : ι → E →L[𝕜] 𝕜)
    (η : ι → ℝ → 𝕜) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) (f : Lp E p unitIntervalMeasure) :
    Lp 𝕜 p unitIntervalMeasure :=
  ∑ i ∈ F, vectorBoundedMultiply (η i) (hη i) (hb i)
    ((π i).compLpL p unitIntervalMeasure f)

theorem jointWeightedReaderVector_ae {ι : Type*} (F : Finset ι)
    (π : ι → E →L[𝕜] 𝕜) (η : ι → ℝ → 𝕜)
    (hη : ∀ i, StronglyMeasurable (η i)) (hb : ∀ i x, ‖η i x‖ ≤ 1)
    (f : Lp E p unitIntervalMeasure) :
    jointWeightedReaderVector F π η hη hb f =ᵐ[unitIntervalMeasure]
      fun x => ∑ i ∈ F, η i x * π i (f x) := by
  let g (i : ι) : Lp 𝕜 p unitIntervalMeasure :=
    vectorBoundedMultiply (η i) (hη i) (hb i) ((π i).compLpL p unitIntervalMeasure f)
  have hg (i : ι) : g i =ᵐ[unitIntervalMeasure] fun x => η i x * π i (f x) := by
    filter_upwards [vectorBoundedMultiplyValue_ae (η i) (hη i) (hb i)
      ((π i).compLpL p unitIntervalMeasure f), (π i).coeFn_compLpL f] with x h₁ h₂
    change g i x = _ at h₁
    simpa only [smul_eq_mul] using h₁.trans (congrArg (fun y => η i x • y) h₂)
  filter_upwards [lpHaar_coeFn_finset_sum F g,
    (F.eventually_all).mpr (fun i _ => hg i)] with x hsum hterm
  change (jointWeightedReaderVector F π η hη hb f) x = _ at hsum
  rw [hsum]
  exact Finset.sum_congr rfl (fun i hi => hterm i hi)

theorem norm_jointWeightedReaderVector_le {ι : Type*} (F : Finset ι)
    (π : ι → E →L[𝕜] 𝕜) (hπ : ∀ y : E, ∑ i ∈ F, ‖π i y‖ ≤ ‖y‖)
    (η : ι → ℝ → 𝕜) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) (f : Lp E p unitIntervalMeasure) :
    ‖jointWeightedReaderVector F π η hη hb f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [jointWeightedReaderVector_ae F π η hη hb f] with x hx
  rw [hx]
  calc
    _ ≤ ∑ i ∈ F, ‖η i x * π i (f x)‖ := norm_sum_le _ _
    _ = ∑ i ∈ F, ‖η i x‖ * ‖π i (f x)‖ := by simp only [norm_mul]
    _ ≤ ∑ i ∈ F, ‖π i (f x)‖ := Finset.sum_le_sum (fun i _ => by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hb i x) (norm_nonneg _))
    _ ≤ ‖f x‖ := hπ (f x)

theorem jointWeightedReader_apply_vector {ι : Type*} (F : Finset ι)
    (π : ι → E →L[𝕜] 𝕜) (η : ι → ℝ → 𝕜)
    (hη : ∀ i, StronglyMeasurable (η i)) (hb : ∀ i x, ‖η i x‖ ≤ 1)
    (f : Lp E p unitIntervalMeasure) :
    jointWeightedReader F π η hη hb f =
      probabilityLpIntegral (𝕜 := 𝕜)
        (jointWeightedReaderVector F π η hη hb f) := by
  simp only [jointWeightedReader, jointWeightedReaderVector,
    ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.comp_apply,
    weightedOuterReader]

theorem norm_jointWeightedReader_le {ι : Type*} (F : Finset ι)
    (π : ι → E →L[𝕜] 𝕜) (hπ : ∀ y : E, ∑ i ∈ F, ‖π i y‖ ≤ ‖y‖)
    (η : ι → ℝ → 𝕜) (hη : ∀ i, StronglyMeasurable (η i))
    (hb : ∀ i x, ‖η i x‖ ≤ 1) :
    ‖jointWeightedReader (p := p) F π η hη hb‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [jointWeightedReader_apply_vector, one_mul]
  calc
    _ ≤ ‖probabilityLpIntegral (𝕜 := 𝕜) (E := 𝕜) (p := p)
        (μ := unitIntervalMeasure)‖ * ‖jointWeightedReaderVector F π η hη hb f‖ :=
      (probabilityLpIntegral (𝕜 := 𝕜) (E := 𝕜) (p := p)
        (μ := unitIntervalMeasure)).le_opNorm (jointWeightedReaderVector F π η hη hb f)
    _ ≤ ‖jointWeightedReaderVector F π η hη hb f‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_probabilityLpIntegral_le (𝕜 := 𝕜) (E := 𝕜) (p := p)
          (μ := unitIntervalMeasure)) (norm_nonneg _)
    _ ≤ ‖f‖ := norm_jointWeightedReaderVector_le F π hπ η hη hb f

end SurveyStatements.P5OperatorReduction
