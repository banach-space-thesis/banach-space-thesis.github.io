import PEMS.SingularFiniteMeasure
import ThesisCommon.Analysis.L1AdjointOneBands

/-! Quantitative singular mass retention on a positive subset of any prescribed
positive input set. This is the singular step of Proposition 4.17. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem singular_smallSet_preserves_adjoint_on_subset
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hSing : IsSingularOperator S)
    (M : Set X) (hM : MeasurableSet M) (hμM : 0 < μ M)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (B : Set Y) (N : Set X) (hB : MeasurableSet B),
      ν B < ENNReal.ofReal δ ∧ MeasurableSet N ∧ N ⊆ M ∧ 0 < μ N ∧
      ∀ x ∈ N, positiveAdjointOneDensity S hS x - ε ≤
        positiveAdjointOneDensity ((lpCutL B hB).comp S) (positive_outputCut_nonneg hS B hB) x := by
  let R := S.comp (lpCutL M hM)
  have hR : 0 ≤ R := positive_inputCut_nonneg hS M hM
  have hRsing : IsSingularOperator R := hSing.inputCut_of_nonneg hS M hM
  have hlow : ‖R‖ - ε / 2 < smallSetSup R univ δ := by
    have hh := alphaTheta_le_smallSetSup R univ MeasurableSet.univ hδ
    rw [singular_finite_alpha_eq_norm R hRsing] at hh
    linarith
  obtain ⟨q, ⟨B, hB, _, hνB, rfl⟩, hq⟩ := exists_lt_of_lt_csSup
    (s := {q : ℝ | ∃ B : Set Y, MeasurableSet B ∧ B ⊆ univ ∧
      ν B < ENNReal.ofReal δ ∧ q = cutOperatorNorm R (univᶜ ∪ B)})
    ⟨_, ∅, MeasurableSet.empty, empty_subset _, by simpa using ENNReal.ofReal_pos.mpr hδ, rfl⟩ hlow
  simp only [compl_univ, empty_union, cutOperatorNorm_eq R B hB] at hq
  let U := (lpCutL B hB).comp S
  have hU : 0 ≤ U := positive_outputCut_nonneg hS B hB
  let Q := U.comp (lpCutL M hM)
  have hQ : 0 ≤ Q := positive_inputCut_nonneg hU M hM
  have hnorm : ‖R‖ - ε / 2 < ‖Q‖ := hq
  let N := M ∩ {x | positiveAdjointOneDensity S hS x - ε ≤ positiveAdjointOneDensity U hU x}
  have hNm : MeasurableSet N := hM.inter (measurableSet_le
    ((measurable_positiveAdjointOneDensity S hS).sub_const ε)
    (measurable_positiveAdjointOneDensity U hU))
  refine ⟨B, N, hB, hνB, hNm, inter_subset_left, ?_, fun x hx => hx.2⟩
  by_contra hNpos
  have hNzero : μ N = 0 := le_antisymm (not_lt.mp hNpos) (zero_le _)
  have hNae : ∀ᵐ x ∂μ, x ∉ N := by simpa only [ae_iff, not_not] using hNzero
  have hReq := positiveAdjointOneDensity_inputCut hS M hM
  have hQeq := positiveAdjointOneDensity_inputCut hU M hM
  have hstrict : ∀ᵐ x ∂μ, x ∈ M → positiveAdjointOneDensity U hU x < ‖R‖ - ε := by
    filter_upwards [hNae, hReq] with x hx hRx hxM
    have hbad : positiveAdjointOneDensity U hU x < positiveAdjointOneDensity S hS x - ε :=
      lt_of_not_ge (fun h => hx ⟨hxM, h⟩)
    have hbound := (positiveAdjointOneDensity_bounds R hR x).2
    change positiveAdjointOneDensity R hR x = _ at hRx
    rw [indicator_of_mem hxM] at hRx
    rw [hRx] at hbound
    linarith
  letI : NeZero (μ.restrict M) := ⟨Measure.restrict_eq_zero.not.mpr hμM.ne'⟩
  have hstrictM := (ae_restrict_iff' hM).mpr hstrict
  obtain ⟨x, hx⟩ := hstrictM.exists
  have hC : 0 ≤ ‖R‖ - ε := (positiveAdjointOneDensity_bounds U hU x).1.trans hx.le
  have hQbound : ‖Q‖ ≤ ‖R‖ - ε := by
    apply (norm_positive_le_iff_adjointDensity hQ hC).mpr
    filter_upwards [hQeq, hstrict] with x hQx hx
    change positiveAdjointOneDensity Q hQ x = _ at hQx
    rw [hQx]
    by_cases hxM : x ∈ M
    · simpa only [indicator_of_mem hxM] using (hx hxM).le
    · simpa only [indicator_of_notMem hxM] using hC
  linarith

end PEMS
