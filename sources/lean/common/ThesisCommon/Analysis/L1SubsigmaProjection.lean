import ThesisCommon.Analysis.L1Subsigma
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1

/-! The actual conditional-expectation projection onto a trimmed L1 subspace.
The norm bound includes the zero-measure case. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
variable {X : Type*} {m₀ : MeasurableSpace X} (μ : @Measure X m₀) [IsFiniteMeasure μ]
variable {m : MeasurableSpace X}

def lOneSubsigmaProjection (hm : m ≤ m₀) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ :=
  condExpL1CLM ℝ hm μ

theorem lOneSubsigmaProjection_mem (hm : m ≤ m₀) (f : Lp ℝ 1 μ) :
    lOneSubsigmaProjection μ hm f ∈ lOneSubsigma μ m :=
  aestronglyMeasurable_condExpL1CLM f

theorem lOneSubsigmaProjection_eq_self (hm : m ≤ m₀) (f : Lp ℝ 1 μ)
    (hf : f ∈ lOneSubsigma μ m) : lOneSubsigmaProjection μ hm f = f :=
  condExpL1CLM_of_aestronglyMeasurable' f hf

theorem range_lOneSubsigmaProjection (hm : m ≤ m₀) :
    Set.range (lOneSubsigmaProjection μ hm) = (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact lOneSubsigmaProjection_mem μ hm g
  · intro hf
    exact ⟨f, lOneSubsigmaProjection_eq_self μ hm f hf⟩

theorem lOneSubsigmaProjection_idempotent (hm : m ≤ m₀) :
    (lOneSubsigmaProjection μ hm).comp (lOneSubsigmaProjection μ hm) =
      lOneSubsigmaProjection μ hm := by
  apply ContinuousLinearMap.ext
  intro f
  exact lOneSubsigmaProjection_eq_self μ hm _ (lOneSubsigmaProjection_mem μ hm f)

theorem norm_lOneSubsigmaProjection_le (hm : m ≤ m₀) : ‖lOneSubsigmaProjection μ hm‖ ≤ 1 :=
  L1.norm_setToL1_le (dominatedFinMeasAdditive_condExpInd ℝ hm μ) zero_le_one

def lOneSubsigmaRetraction (hm : m ≤ m₀) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (μ.trim hm) :=
  lOneSubsigmaLift μ hm (lOneSubsigmaProjection μ hm) (lOneSubsigmaProjection_mem μ hm)

theorem lOneSubsigmaRetraction_embedding (hm : m ≤ m₀) :
    (lOneSubsigmaRetraction μ hm).comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (Lp ℝ 1 (μ.trim hm)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (lOneSubsigmaEmbedding μ hm).injective
  have hcomp := lOneSubsigmaEmbedding_lift μ hm (lOneSubsigmaProjection μ hm)
    (lOneSubsigmaProjection_mem μ hm)
  have h := DFunLike.congr_fun hcomp (lOneSubsigmaEmbedding μ hm f)
  change lOneSubsigmaEmbedding μ hm
    (lOneSubsigmaRetraction μ hm (lOneSubsigmaEmbedding μ hm f)) = lOneSubsigmaEmbedding μ hm f
  apply h.trans
  apply lOneSubsigmaProjection_eq_self μ hm
  change lOneSubsigmaEmbedding μ hm f ∈ (lOneSubsigma μ m : Set (Lp ℝ 1 μ))
  rw [← range_lOneSubsigmaEmbedding μ hm]
  exact mem_range_self f

theorem norm_lOneSubsigmaRetraction_le (hm : m ≤ m₀) : ‖lOneSubsigmaRetraction μ hm‖ ≤ 1 := by
  rw [lOneSubsigmaRetraction, norm_lOneSubsigmaLift]
  exact norm_lOneSubsigmaProjection_le μ hm

end ThesisCommon
