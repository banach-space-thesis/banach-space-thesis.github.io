import ThesisCommon.Analysis.L1LocalizedIntegralPart
import ThesisCommon.Analysis.L1AdjointOneBands

/-! Actual local band-cut decomposition and its adjoint-at-one masses. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lebesgueL1Extend_restrict_eq_cut (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (f : Lp ℝ 1 ν) :
    lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (lebesgueLpRestrict (𝕜 := ℝ) Θ f) = lpCut Θ hΘ f := by
  apply Lp.ext
  filter_upwards [lebesgueLpExtend_coe (𝕜 := ℝ) Θ hΘ (lebesgueLpRestrict (𝕜 := ℝ) Θ f),
    (ae_restrict_iff' hΘ).mp (lebesgueLpRestrict_coe (𝕜 := ℝ) Θ f), lpCut_coe Θ hΘ f]
    with y he hr hc
  rw [he, hc]
  by_cases hy : y ∈ Θ <;> simp [hy, hr]

theorem lOne_localized_cut_decomposition (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (Θ B : Set Y) (hΘ : MeasurableSet Θ) (hB : MeasurableSet B) :
    (lpCutL Θᶜ hΘ.compl).comp T +
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
        ((lpCutL B hB).comp ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T)) =
      (lpCutL (Θᶜ ∪ (B ∩ Θ)) (hΘ.compl.union (hB.inter hΘ))).comp T := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (lpCut Θᶜ hΘ.compl (T f))
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (lpCut B hB (lebesgueLpRestrict (𝕜 := ℝ) Θ (T f)))),
    lpCut_coe Θᶜ hΘ.compl (T f),
    lebesgueLpExtend_coe (𝕜 := ℝ) Θ hΘ (lpCut B hB (lebesgueLpRestrict (𝕜 := ℝ) Θ (T f))),
    (ae_restrict_iff' hΘ).mp (lpCut_coe B hB (lebesgueLpRestrict (𝕜 := ℝ) Θ (T f))),
    (ae_restrict_iff' hΘ).mp (lebesgueLpRestrict_coe (𝕜 := ℝ) Θ (T f)),
    lpCut_coe (Θᶜ ∪ (B ∩ Θ)) (hΘ.compl.union (hB.inter hΘ)) (T f)] with y ha ho he hb hr hc
  change (lpCut Θᶜ hΘ.compl (T f) + lebesgueLpExtend (𝕜 := ℝ) Θ hΘ
    (lpCut B hB (lebesgueLpRestrict (𝕜 := ℝ) Θ (T f)))) y =
      lpCut (Θᶜ ∪ (B ∩ Θ)) (hΘ.compl.union (hB.inter hΘ)) (T f) y
  rw [ha, Pi.add_apply, ho, he, hc]
  by_cases hyΘ : y ∈ Θ <;> by_cases hyB : y ∈ B <;> simp [hyΘ, hyB, hb, hr]

theorem lOne_localized_decomposition (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) :
    (lpCutL Θᶜ hΘ.compl).comp T +
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
        ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  change lpCut Θᶜ hΘ.compl (T f) +
    lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (lebesgueLpRestrict (𝕜 := ℝ) Θ (T f)) = T f
  rw [lebesgueL1Extend_restrict_eq_cut, add_comm]
  exact lOneCut_add_compl Θ hΘ (T f)

variable [IsFiniteMeasure μ]

theorem positiveAdjointOneDensity_extend (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)) (hK : 0 ≤ K) :
    positiveAdjointOneDensity ((lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp K)
      (lebesgueL1Extend_comp_nonneg Θ hΘ hK) =ᵐ[μ] positiveAdjointOneDensity K hK := by
  have h := (positiveAdjointOne_coe
    ((lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp K)
    (lebesgueL1Extend_comp_nonneg Θ hΘ hK)).symm
  rw [positiveAdjointOne_extend Θ hΘ K hK] at h
  exact h.trans (positiveAdjointOne_coe K hK)

theorem positiveAdjointOneDensity_add_extend (Θ : Set Y) (hΘ : MeasurableSet Θ)
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : 0 ≤ S)
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)} (hK : 0 ≤ K) :
    positiveAdjointOneDensity (S + (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp K)
      (add_nonneg hS (lebesgueL1Extend_comp_nonneg Θ hΘ hK)) =ᵐ[μ]
      fun x => positiveAdjointOneDensity S hS x + positiveAdjointOneDensity K hK x := by
  filter_upwards [positiveAdjointOneDensity_add hS (lebesgueL1Extend_comp_nonneg Θ hΘ hK),
    positiveAdjointOneDensity_extend Θ hΘ K hK] with x ha he
  exact ha.trans (congrArg (_ + ·) he)

theorem localizedIntegralRemainder_eq_outside_add_extend (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [SigmaFinite (ν.restrict Θ)] (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    localizedIntegralRemainder Θ hΘ T = (lpCutL Θᶜ hΘ.compl).comp T +
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
        ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T - localizedIntegralPart Θ T) := by
  rw [ContinuousLinearMap.comp_sub, ← add_sub_assoc, lOne_localized_decomposition]
  rfl

end ThesisCommon
