import ThesisCommon.Analysis.QuotientRealScalarization
import ThesisCommon.Analysis.InfinityQuotientScalarMasks
import ThesisCommon.Analysis.InfinityIndicatorDetermination

/-! Drewnowski--Roberts scalar compression on the actual quotient over
real or complex scalars. The real measure theorem is applied successively
to the two scalar components, then indicator approximation gives all vectors. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
variable {𝕜 : Type*} [RCLike 𝕜]

def quotientRealMeasureOfMap
    (S : InfinityCZeroQuotient 𝕜 →L[ℝ] InfinityCZeroQuotient ℝ) : QuotientRealMeasure where
  value A := S (infinityQuotientIndicator (𝕜 := 𝕜) A)
  empty := by rw [infinityQuotientIndicator_empty, map_zero]
  union A B h := by rw [infinityQuotientIndicator_union h, map_add]
  remove_finite A K h := by rw [infinityQuotientIndicator_remove_finite A K h]
  bound := ‖S‖
  norm_le A := (S.le_opNorm _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (norm_infinityQuotientIndicator_le (𝕜 := 𝕜) A) (norm_nonneg S))

theorem exists_infinityQuotient_indicator_scalarization
    (T : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜)
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ c : 𝕜,
      ∀ F : Set ℕ, F ⊆ B →
        infinityQuotientMask (𝕜 := 𝕜) B (T (infinityQuotientIndicator (𝕜 := 𝕜) F)) =
          c • infinityQuotientIndicator (𝕜 := 𝕜) F := by
  let μr := quotientRealMeasureOfMap ((infinityQuotientRe (𝕜 := 𝕜)).comp (T.restrictScalars ℝ))
  let μi := quotientRealMeasureOfMap ((infinityQuotientIm (𝕜 := 𝕜)).comp (T.restrictScalars ℝ))
  obtain ⟨A', hA', hA'A, a, ha⟩ := μr.exists_scalar_subset hA
  obtain ⟨B, hB, hBA', b, hb⟩ := μi.exists_scalar_subset hA'
  have hre (F : Set ℕ) (hF : F ⊆ B) (U : FreeNatUltrafilter) (hU : B ∈ U) :
      RCLike.re (infinityQuotientEval (𝕜 := 𝕜) U
        (T (infinityQuotientIndicator (𝕜 := 𝕜) F))) = if F ∈ U then a else 0 := by
    have h := ha F (hF.trans hBA') U (Filter.mem_of_superset hU hBA')
    simpa only [QuotientRealMeasure.eval, μr, quotientRealMeasureOfMap,
      ContinuousLinearMap.comp_apply,
      infinityQuotientEval_re] using h
  have him (F : Set ℕ) (hF : F ⊆ B) (U : FreeNatUltrafilter) (hU : B ∈ U) :
      RCLike.im (infinityQuotientEval (𝕜 := 𝕜) U
        (T (infinityQuotientIndicator (𝕜 := 𝕜) F))) = if F ∈ U then b else 0 := by
    have h := hb F hF U hU
    simpa only [QuotientRealMeasure.eval, μi, quotientRealMeasureOfMap,
      ContinuousLinearMap.comp_apply,
      infinityQuotientEval_im] using h
  obtain ⟨V, hV⟩ := FreeNatUltrafilter.exists_mem hB
  let c := infinityQuotientEval (𝕜 := 𝕜) V (T (infinityQuotientIndicator (𝕜 := 𝕜) B))
  have hcr : RCLike.re c = a := by simpa only [if_pos hV] using hre B Set.Subset.rfl V hV
  have hci : RCLike.im c = b := by simpa only [if_pos hV] using him B Set.Subset.rfl V hV
  refine ⟨B, hB, hBA'.trans hA'A, c, fun F hF => ?_⟩
  apply infinityQuotient_ext
  intro U
  rw [infinityQuotientEval_mask, map_smul, infinityQuotientEval_indicator]
  by_cases hU : B ∈ U
  · rw [if_pos hU]
    by_cases hFU : F ∈ U
    · rw [if_pos hFU, smul_eq_mul, mul_one]
      apply RCLike.ext
      · simpa only [if_pos hFU, hcr] using hre F hF U hU
      · simpa only [if_pos hFU, hci] using him F hF U hU
    · rw [if_neg hFU, smul_zero]
      apply RCLike.ext
      · simpa only [if_neg hFU, map_zero] using hre F hF U hU
      · simpa only [if_neg hFU, map_zero] using him F hF U hU
  · have hFU : F ∉ U := fun hFU => hU (Filter.mem_of_superset hFU hF)
    rw [if_neg hU, if_neg hFU, smul_zero]

@[simp] theorem infinityQuotientMk_indicator (A : Set ℕ) :
    infinityQuotientMk (𝕜 := 𝕜) (infinityIndicator (𝕜 := 𝕜) A) =
      infinityQuotientIndicator (𝕜 := 𝕜) A := by
  unfold infinityQuotientIndicator
  congr 1

theorem exists_infinityQuotient_scalar_compression
    (T : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜)
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ c : 𝕜,
      ((infinityQuotientMask (𝕜 := 𝕜) B).comp T).comp (infinityQuotientMask (𝕜 := 𝕜) B) =
        c • infinityQuotientMask (𝕜 := 𝕜) B := by
  obtain ⟨B, hB, hBA, c, hc⟩ := exists_infinityQuotient_indicator_scalarization T hA
  have hvector (x : lp (fun _ : ℕ => 𝕜) ∞) (hx : ∀ i ∉ B, x i = 0) :
      infinityQuotientMask (𝕜 := 𝕜) B (T (infinityQuotientMk (𝕜 := 𝕜) x)) =
        c • infinityQuotientMk (𝕜 := 𝕜) x := by
    apply infinity_operator_eq_on_supported_of_indicators
      (((infinityQuotientMask (𝕜 := 𝕜) B).comp T).comp (infinityQuotientMk (𝕜 := 𝕜)))
      (c • infinityQuotientMk (𝕜 := 𝕜)) (B := B) _ x hx
    intro F hF
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      infinityQuotientMk_indicator] using hc F hF
  refine ⟨B, hB, hBA, c, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x =>
    change infinityQuotientMask (𝕜 := 𝕜) B
      (T (infinityQuotientMask (𝕜 := 𝕜) B (infinityQuotientMk (𝕜 := 𝕜) x))) =
        c • infinityQuotientMask (𝕜 := 𝕜) B (infinityQuotientMk (𝕜 := 𝕜) x)
    rw [infinityQuotientMask_mk]
    apply hvector
    intro n hn
    simp only [infinityMask_apply, if_neg hn]

end ThesisCommon
