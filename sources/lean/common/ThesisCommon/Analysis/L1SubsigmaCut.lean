import ThesisCommon.Analysis.L1Subsigma
import ThesisCommon.LpCut

/-! Measurable output cutoffs commute with the actual trimmed-L1 embedding. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
variable {X : Type*} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)
variable {m : MeasurableSpace X}

theorem lOneSubsigmaEmbedding_cut (hm : m ≤ m₀) (A : Set X)
    (hA : MeasurableSet[m] A) (f : Lp ℝ 1 (μ.trim hm)) :
    lOneSubsigmaEmbedding μ hm (lpCut A hA f) =
      @lpCut ℝ _ X m₀ μ 1 A (hm A hA) (lOneSubsigmaEmbedding μ hm f) := by
  apply Lp.ext
  filter_upwards [lOneSubsigmaEmbedding_ae_eq μ hm (lpCut A hA f),
    ae_eq_of_ae_eq_trim (lpCut_coe A hA f),
    @lpCut_coe ℝ _ X m₀ μ 1 A (hm A hA) (lOneSubsigmaEmbedding μ hm f),
    lOneSubsigmaEmbedding_ae_eq μ hm f] with x h1 h2 h3 h4
  rw [h1, h2, h3]
  by_cases hx : x ∈ A <;> simp [hx, h4]

end ThesisCommon
