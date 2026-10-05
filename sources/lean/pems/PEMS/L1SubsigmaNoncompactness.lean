import PEMS.L1WeakNoncompactness
import ThesisCommon.Analysis.L1SubsigmaCut

/-! Restricting the input to a trimmed L1 space and lifting the output
into another trimmed L1 space cannot increase the small-set functional.
The comparisons use actual isometric embeddings and measurable cutoffs. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace PEMS
open ThesisCommon
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀}
variable {m : MeasurableSpace X} {n : MeasurableSpace Y}

theorem cutOperatorNorm_lOneSubsigmaLift_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hm : m ≤ m₀) (hn : n ≤ n₀)
    (hmap : ∀ f, T (lOneSubsigmaEmbedding μ hm f) ∈ lOneSubsigma ν n)
    (A : Set Y) (hA : MeasurableSet[n] A) :
    cutOperatorNorm (lOneSubsigmaLift ν hn
      (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap) A ≤
      @cutOperatorNorm ℝ _ X Y m₀ n₀ μ ν T A := by
  rw [cutOperatorNorm_eq _ A hA, @cutOperatorNorm_eq ℝ _ X Y m₀ n₀ μ ν T A (hn A hA)]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖lpCut A hA (lOneSubsigmaLift ν hn
    (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap f)‖ ≤ _
  rw [← (lOneSubsigmaEmbedding ν hn).norm_map, lOneSubsigmaEmbedding_cut]
  have heq := DFunLike.congr_fun (lOneSubsigmaEmbedding_lift ν hn
    (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap) f
  change lOneSubsigmaEmbedding ν hn (lOneSubsigmaLift ν hn
    (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap f) =
      T (lOneSubsigmaEmbedding μ hm f) at heq
  rw [heq]
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.norm_map] using
    ((@lpCutL ℝ _ Y n₀ ν 1 _ A (hn A hA)).comp T).le_opNorm (lOneSubsigmaEmbedding μ hm f)

theorem smallSetSup_univ_lOneSubsigmaLift_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hm : m ≤ m₀) (hn : n ≤ n₀)
    (hmap : ∀ f, T (lOneSubsigmaEmbedding μ hm f) ∈ lOneSubsigma ν n)
    {δ : ℝ} (hδ : 0 < δ) :
    smallSetSup (lOneSubsigmaLift ν hn
      (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap) univ δ ≤
      @smallSetSup ℝ _ X Y m₀ n₀ μ ν T univ δ := by
  apply csSup_le
  · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
    simpa using ENNReal.ofReal_pos.mpr hδ
  · rintro q ⟨B, hB, _, hνB, rfl⟩
    simp only [compl_univ, empty_union]
    rw [trim_measurableSet_eq hn hB] at hνB
    have hh := @cutOperatorNorm_le_smallSetSup ℝ _ X Y m₀ n₀ μ ν T univ MeasurableSet.univ δ B
      (hn B hB) (subset_univ B) hνB
    simp only [compl_univ, empty_union] at hh
    exact (cutOperatorNorm_lOneSubsigmaLift_le T hm hn hmap B hB).trans hh

theorem alphaTheta_univ_lOneSubsigmaLift_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hm : m ≤ m₀) (hn : n ≤ n₀)
    (hmap : ∀ f, T (lOneSubsigmaEmbedding μ hm f) ∈ lOneSubsigma ν n) :
    alphaTheta (lOneSubsigmaLift ν hn
      (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap) univ ≤
      @alphaTheta ℝ _ X Y m₀ n₀ μ ν T univ := by
  apply le_csInf
  · exact ⟨_, 1, zero_lt_one, rfl⟩
  · rintro r ⟨δ, hδ, rfl⟩
    exact (alphaTheta_le_smallSetSup _ univ MeasurableSet.univ hδ).trans
      (smallSetSup_univ_lOneSubsigmaLift_le T hm hn hmap hδ)

theorem localizedWeakNoncompactness_lOneSubsigmaLift_le [IsFiniteMeasure ν]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hm : m ≤ m₀) (hn : n ≤ n₀)
    (hmap : ∀ f, T (lOneSubsigmaEmbedding μ hm f) ∈ lOneSubsigma ν n) :
    localizedWeakNoncompactness (lOneSubsigmaLift ν hn
      (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap) ≤
      @localizedWeakNoncompactness ℝ _ X Y m₀ n₀ μ ν T := by
  simpa only [localizedWeakNoncompactness_eq_alphaTheta_univ] using
    alphaTheta_univ_lOneSubsigmaLift_le T hm hn hmap

end PEMS
