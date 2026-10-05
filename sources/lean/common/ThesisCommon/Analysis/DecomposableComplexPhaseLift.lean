import ThesisCommon.Analysis.ComplexL1LocalizedPhase
import ThesisCommon.Analysis.ComplexL1BoundedRangeDomination
import ThesisCommon.Analysis.L1BoundedRangeIntegral
import ThesisCommon.Analysis.DecomposableL1Order

/-! Exact complex phase lifting over an arbitrary measurable finite-measure
partition. The pieces are assembled by the actual L1 direct-sum operator;
bounded-range approximation supplies integrality on each finite piece. -/
noncomputable section
open MeasureTheory Set
open scoped Function ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lOneOperator_eq_of_decomposable_pieces {𝕜 : Type*} [RCLike 𝕜]
    (s : I → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (T U : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (h : ∀ i, T.comp (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)).toContinuousLinearMap =
      U.comp (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)).toContinuousLinearMap) : T = U := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply decomposableL1Operator_norm_le_of_pieces s hs hd hμ (T - U) 0 le_rfl
  intro i
  rw [ContinuousLinearMap.sub_comp, h i, sub_self, norm_zero]

theorem exists_decomposable_complex_localized_phaseLift
    (s : I → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    [∀ i, IsFiniteMeasure (μ.restrict (s i))]
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)) (hH : 0 ≤ H)
    (hApprox : HasPositiveBoundedRangeApproximants H)
    (hHM : (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H ≤
      complexL1OperatorModulus T) :
    ∃ V : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 (ν.restrict Θ), IsWeaklyCompactOperator V ∧
      complexL1OperatorModulus V = H ∧
      complexL1OperatorModulus (T - (lebesgueLpExtend (𝕜 := ℂ) Θ hΘ).toContinuousLinearMap.comp V) =
        complexL1OperatorModulus T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H := by
  have hHi : H ≤ (lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (complexL1OperatorModulus T) := by
    intro f hf
    have hh := positive_operator_monotone
      (show 0 ≤ lebesgueLpRestrict (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν) Θ from
        fun g hg => lebesgueL1Restrict_nonneg Θ g hg) (hHM f hf)
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      lebesgueLpRestrict_extend] using hh
  let Jr := fun i => (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1)
    (μ := μ) (s i) (hs i)).toContinuousLinearMap
  let Jc := fun i => (lebesgueLpExtend (𝕜 := ℂ) (E := ℂ) (p := 1)
    (μ := μ) (s i) (hs i)).toContinuousLinearMap
  have hp : ∀ i, ∃ V : Lp ℂ 1 (μ.restrict (s i)) →L[ℂ] Lp ℂ 1 (ν.restrict Θ),
      IsIntegralOperator V ∧ complexL1OperatorModulus V = H.comp (Jr i) ∧
      complexL1OperatorModulus (T.comp (Jc i) -
        (lebesgueLpExtend (𝕜 := ℂ) Θ hΘ).toContinuousLinearMap.comp V) =
        complexL1OperatorModulus (T.comp (Jc i)) -
          (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp (H.comp (Jr i)) := by
    intro i
    apply exists_complex_localized_integral_phaseLift (T.comp (Jc i)) Θ hΘ
      (H.comp (Jr i))
    · exact fun f hf => hH _ (lebesgueL1Extend_nonneg (s i) (hs i) f hf)
    · exact hApprox.isIntegral_comp_lebesgueLpExtend (s i) (hs i)
    · dsimp only [Jc]
      rw [complexL1OperatorModulus_inputExtend T (s i) (hs i)]
      exact fun f hf => hHi _ (lebesgueL1Extend_nonneg (s i) (hs i) f hf)
  choose A hAI hAM hAE using hp
  have hA : ∀ i, ‖A i‖ ≤ ‖H‖ := by
    intro i
    rw [← norm_complexL1OperatorModulus, hAM i]
    exact (H.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg H)
      (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := μ) (s i) (hs i)).norm_toContinuousLinearMap_le)
  let V := decomposableL1Operator s hμ A ‖H‖ (norm_nonneg H) hA
  have hVp : ∀ i, V.comp (Jc i) = A i := by
    intro i
    apply ContinuousLinearMap.ext
    intro f
    exact decomposableL1Operator_extend s hs hd hμ A ‖H‖ (norm_nonneg H) hA i f
  have hVM : complexL1OperatorModulus V = H := by
    apply lOneOperator_eq_of_decomposable_pieces s hs hd hμ
    intro i
    change (complexL1OperatorModulus V).comp (Jr i) = H.comp (Jr i)
    rw [← complexL1OperatorModulus_inputExtend V (s i) (hs i)]
    change complexL1OperatorModulus (V.comp (Jc i)) = _
    rw [hVp i, hAM i]
  refine ⟨V, hApprox.weaklyCompact_of_complex_modulus_le hVM.le, hVM, ?_⟩
  apply lOneOperator_eq_of_decomposable_pieces s hs hd hμ
  intro i
  rw [← complexL1OperatorModulus_inputExtend _ (s i) (hs i)]
  change complexL1OperatorModulus ((T -
    (lebesgueLpExtend (𝕜 := ℂ) Θ hΘ).toContinuousLinearMap.comp V).comp (Jc i)) = _
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc, hVp i, hAE i]
  dsimp only [Jc]
  rw [complexL1OperatorModulus_inputExtend T (s i) (hs i),
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]

end ThesisCommon
