import ThesisCommon.Analysis.ComplexL1Restrictions

/-! The genuine complex operator modulus commutes with input band inclusions
and output restriction or zero extension, for arbitrary measures. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

private theorem dominates_real (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    complexL1Modulus (T (complexL1OfReal μ f)) ≤ complexL1OperatorModulus T f :=
  complexOperatorModulus_dominates_nonneg (complexL1OperatorRealRestriction T) f hf

private theorem cut_nonneg (A : Set X) (hA : MeasurableSet A)
    (f : Lp ℝ 1 μ) (hf : 0 ≤ f) : 0 ≤ lpCut A hA f := by
  have h := lOneCut_mono A hA hf
  change lpCutL (𝕜 := ℝ) (p := 1) A hA 0 ≤ lpCutL A hA f at h
  simpa only [map_zero] using h

theorem complexL1OperatorModulus_inputExtend
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (A : Set X) (hA : MeasurableSet A) :
    complexL1OperatorModulus (T.comp (lebesgueLpExtend (𝕜 := ℂ) A hA).toContinuousLinearMap) =
      (complexL1OperatorModulus T).comp (lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap := by
  let U := T.comp (lebesgueLpExtend (𝕜 := ℂ) A hA).toContinuousLinearMap
  apply le_antisymm
  · apply complexL1OperatorModulus_least
    intro f hf
    change complexL1Modulus (T (lebesgueLpExtend (𝕜 := ℂ) A hA
      (complexL1OfReal (μ.restrict A) f))) ≤ complexL1OperatorModulus T
        (lebesgueLpExtend (𝕜 := ℝ) A hA f)
    rw [complexL1OfReal_extend]
    exact dominates_real T _ (lebesgueL1Extend_nonneg A hA f hf)
  · let D := (complexL1OperatorModulus U).comp (lebesgueLpRestrict (𝕜 := ℝ) A) +
      (complexL1OperatorModulus T).comp (lpCutL Aᶜ hA.compl)
    have hD : ∀ f : Lp ℝ 1 μ, 0 ≤ f →
        complexL1Modulus (T (complexL1OfReal μ f)) ≤ D f := by
      intro f hf
      have heq : complexL1OfReal μ f =
          lebesgueLpExtend (𝕜 := ℂ) A hA
            (complexL1OfReal (μ.restrict A) (lebesgueLpRestrict (𝕜 := ℝ) A f)) +
            complexL1OfReal μ (lpCut Aᶜ hA.compl f) := by
        rw [← complexL1OfReal_restrict, lebesgueLpExtend_restrict_eq_cut_rclike,
          complexL1OfReal_cut]
        exact (lpCut_add_compl_rclike A hA _).symm
      calc
        complexL1Modulus (T (complexL1OfReal μ f)) =
            complexL1Modulus (U (complexL1OfReal (μ.restrict A) (lebesgueLpRestrict (𝕜 := ℝ) A f)) +
              T (complexL1OfReal μ (lpCut Aᶜ hA.compl f))) := by
          conv_lhs => rw [heq, map_add]
          rfl
        _ ≤ complexL1Modulus (U (complexL1OfReal (μ.restrict A) (lebesgueLpRestrict (𝕜 := ℝ) A f))) +
            complexL1Modulus (T (complexL1OfReal μ (lpCut Aᶜ hA.compl f))) :=
          complexL1Modulus_add_le _ _
        _ ≤ D f := add_le_add
          (dominates_real U _ (lebesgueL1Restrict_nonneg A f hf))
          (dominates_real T _ (cut_nonneg Aᶜ hA.compl f hf))
    intro f hf
    have h := complexL1OperatorModulus_least T D hD
      (lebesgueLpExtend (𝕜 := ℝ) A hA f) (lebesgueL1Extend_nonneg A hA f hf)
    change complexL1OperatorModulus T (lebesgueLpExtend (𝕜 := ℝ) A hA f) ≤
      complexL1OperatorModulus U (lebesgueLpRestrict (𝕜 := ℝ) A
        (lebesgueLpExtend (𝕜 := ℝ) A hA f)) +
        complexL1OperatorModulus T (lpCut Aᶜ hA.compl (lebesgueLpExtend (𝕜 := ℝ) A hA f)) at h
    simpa only [lebesgueLpRestrict_extend, lpCut_compl_extend, map_zero, add_zero] using h

theorem complexL1OperatorModulus_outputExtend (A : Set Y) (hA : MeasurableSet A)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 (ν.restrict A)) :
    complexL1OperatorModulus ((lebesgueLpExtend (𝕜 := ℂ) A hA).toContinuousLinearMap.comp T) =
      (lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap.comp (complexL1OperatorModulus T) := by
  let U := (lebesgueLpExtend (𝕜 := ℂ) A hA).toContinuousLinearMap.comp T
  apply le_antisymm
  · apply complexL1OperatorModulus_least
    intro f hf
    change complexL1Modulus (lebesgueLpExtend (𝕜 := ℂ) A hA (T (complexL1OfReal μ f))) ≤
      lebesgueLpExtend (𝕜 := ℝ) A hA (complexL1OperatorModulus T f)
    rw [complexL1Modulus_extend]
    exact lebesgueL1Extend_mono A hA (dominates_real T f hf)
  · have hM : complexL1OperatorModulus T ≤
        (lebesgueLpRestrict (𝕜 := ℝ) A).comp (complexL1OperatorModulus U) := by
      apply complexL1OperatorModulus_least
      intro f hf
      have h := positive_operator_monotone
        (show 0 ≤ lebesgueLpRestrict (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν) A from
          fun g hg => lebesgueL1Restrict_nonneg A g hg) (dominates_real U f hf)
      change lebesgueLpRestrict (𝕜 := ℝ) A
        (complexL1Modulus (lebesgueLpExtend (𝕜 := ℂ) A hA (T (complexL1OfReal μ f)))) ≤ _ at h
      rw [complexL1Modulus_extend, lebesgueLpRestrict_extend] at h
      exact h
    intro f hf
    exact (lebesgueL1Extend_mono A hA (hM f hf)).trans
      (lebesgueL1Extend_restrict_le A hA _ (complexL1OperatorModulus_nonneg U f hf))

theorem complexL1OperatorModulus_outputRestrict
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (A : Set Y) (hA : MeasurableSet A) :
    complexL1OperatorModulus ((lebesgueLpRestrict (𝕜 := ℂ) A).comp T) =
      (lebesgueLpRestrict (𝕜 := ℝ) A).comp (complexL1OperatorModulus T) := by
  have heq : (lebesgueLpExtend (𝕜 := ℂ) A hA).toContinuousLinearMap.comp
      ((lebesgueLpRestrict (𝕜 := ℂ) A).comp T) = (lpCutL A hA).comp T := by
    apply ContinuousLinearMap.ext
    intro f
    exact lebesgueLpExtend_restrict_eq_cut_rclike A hA (T f)
  apply ContinuousLinearMap.ext
  intro f
  apply (lebesgueLpExtend (𝕜 := ℝ) A hA).injective
  calc
    _ = complexL1OperatorModulus ((lebesgueLpExtend (𝕜 := ℂ) A hA).toContinuousLinearMap.comp
          ((lebesgueLpRestrict (𝕜 := ℂ) A).comp T)) f :=
      (DFunLike.congr_fun (complexL1OperatorModulus_outputExtend A hA
        ((lebesgueLpRestrict (𝕜 := ℂ) A).comp T)) f).symm
    _ = lpCut A hA (complexL1OperatorModulus T f) := by
      rw [heq, complexL1OperatorModulus_outputCut]
      rfl
    _ = _ := (lebesgueL1Extend_restrict_eq_cut A hA _).symm

end ThesisCommon
