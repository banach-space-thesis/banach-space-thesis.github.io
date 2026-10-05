import ThesisCommon.Analysis.L1AdjointOne
import ThesisCommon.Analysis.L1CutModulus
import ThesisCommon.Analysis.IntegralOperatorBand

/-! Input and output band cuts for positive adjoint-at-one representatives,
and solidity of the genuine singular-operator predicate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem IsSingularOperator.of_abs_le {S R : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : IsSingularOperator S) (hR : |R| ≤ |S|) : IsSingularOperator R := by
  intro K hK
  apply le_antisymm
  · exact (inf_le_inf_right |K| hR).trans_eq (hS K hK)
  · exact le_inf (abs_nonneg R) (abs_nonneg K)

theorem positive_inputCut_nonneg {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) (A : Set X) (hA : MeasurableSet A) :
    0 ≤ S.comp (lpCutL A hA) := by
  intro f hf
  apply hS
  have h := lOneCut_mono A hA hf
  change lpCutL (𝕜 := ℝ) (p := 1) A hA 0 ≤ lpCutL A hA f at h
  simpa only [map_zero] using h

theorem positive_inputCut_le {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) (A : Set X) (hA : MeasurableSet A) :
    S.comp (lpCutL A hA) ≤ S := by
  intro f hf
  exact (positive_operator_monotone hS) (lOneCut_le_self A hA hf)

theorem IsSingularOperator.inputCut_of_nonneg {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : IsSingularOperator S) (hpos : 0 ≤ S) (A : Set X) (hA : MeasurableSet A) :
    IsSingularOperator (S.comp (lpCutL A hA)) := by
  apply hS.of_abs_le
  rw [abs_of_nonneg hpos, abs_of_nonneg (positive_inputCut_nonneg hpos A hA)]
  exact positive_inputCut_le hpos A hA

variable [IsFiniteMeasure μ]

theorem positiveAdjointOneDensity_congr {S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (h : S = T) :
    positiveAdjointOneDensity S hS = positiveAdjointOneDensity T hT := by
  subst T
  rfl

theorem positive_outputCut_nonneg {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) (B : Set Y) (hB : MeasurableSet B) :
    0 ≤ (lpCutL B hB).comp S := by
  intro f hf
  have h := lOneCut_mono B hB (hS f hf)
  change lpCutL (𝕜 := ℝ) (p := 1) B hB 0 ≤ lpCutL B hB (S f) at h
  simpa only [map_zero] using h

theorem norm_positive_le_iff_adjointDensity {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) {C : ℝ} (hC : 0 ≤ C) :
    ‖S‖ ≤ C ↔ ∀ᵐ x ∂μ, positiveAdjointOneDensity S hS x ≤ C := by
  constructor
  · intro h
    exact Eventually.of_forall fun x => (positiveAdjointOneDensity_bounds S hS x).2.trans h
  · intro h
    rw [← norm_positiveAdjointOne S hS]
    apply linfty_norm_le_of_ae_bound _ hC
    filter_upwards [positiveAdjointOne_coe S hS, h] with x hx hbound
    rw [hx, Real.norm_of_nonneg (positiveAdjointOneDensity_bounds S hS x).1]
    exact hbound

theorem positive_outputCut_mono_set {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) {B H : Set Y} (hB : MeasurableSet B) (hH : MeasurableSet H) (hBH : B ⊆ H) :
    (lpCutL B hB).comp S ≤ (lpCutL H hH).comp S := by
  intro f hf
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [lpCut_coe B hB (S f), lpCut_coe H hH (S f),
    (Lp.coeFn_nonneg (S f)).mpr (hS f hf)] with y h1 h2 hp
  change lpCut B hB (S f) y ≤ lpCut H hH (S f) y
  rw [h1, h2]
  change 0 ≤ S f y at hp
  by_cases hyB : y ∈ B
  · simp [hyB, hBH hyB]
  · by_cases hyH : y ∈ H <;> simp [hyB, hyH, hp]

theorem positiveAdjointOneDensity_add {S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    positiveAdjointOneDensity (S + T) (add_nonneg hS hT) =ᵐ[μ]
      fun x => positiveAdjointOneDensity S hS x + positiveAdjointOneDensity T hT x := by
  have heq := (positiveAdjointOne_coe (S + T) (add_nonneg hS hT)).symm
  rw [positiveAdjointOne_add S T hS hT] at heq
  filter_upwards [heq, Lp.coeFn_add (positiveAdjointOne S hS) (positiveAdjointOne T hT),
    positiveAdjointOne_coe S hS, positiveAdjointOne_coe T hT] with x h1 h2 h3 h4
  simpa only [h1, h2, Pi.add_apply, h3, h4]

theorem lOneCut_indicator (A M : Set X) (hA : MeasurableSet A) (hM : MeasurableSet M) :
    lpCut M hM (lOneIndicator μ A hA) = lOneIndicator μ (A ∩ M) (hA.inter hM) := by
  apply Lp.ext
  filter_upwards [lpCut_coe M hM (lOneIndicator μ A hA), lOneIndicator_coe (μ := μ) A hA,
    lOneIndicator_coe (μ := μ) (A ∩ M) (hA.inter hM)] with x h1 h2 h3
  rw [h1, h3]
  by_cases hxM : x ∈ M <;> by_cases hxA : x ∈ A <;> simp [hxM, hxA, h2]

theorem positiveAdjointOneDensity_inputCut {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) (M : Set X) (hM : MeasurableSet M) :
    positiveAdjointOneDensity (S.comp (lpCutL M hM)) (positive_inputCut_nonneg hS M hM)
      =ᵐ[μ] M.indicator (positiveAdjointOneDensity S hS) := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => ((positiveAdjointOneDensity_memLp _ _).integrable le_top).integrableOn)
    (fun _ _ _ => (((positiveAdjointOneDensity_memLp S hS).integrable le_top).indicator hM).integrableOn)
  intro A hA _
  rw [positiveAdjointOneDensity_indicator, setIntegral_indicator hM,
    positiveAdjointOneDensity_indicator]
  change (∫ y, S (lpCut M hM (lOneIndicator μ A hA)) y ∂ν) = _
  rw [lOneCut_indicator]

theorem positiveAdjointOneDensity_mono {S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T) :
    positiveAdjointOneDensity S hS ≤ᵐ[μ] positiveAdjointOneDensity T hT := by
  apply ae_le_of_forall_setIntegral_le
    ((positiveAdjointOneDensity_memLp S hS).integrable le_top)
    ((positiveAdjointOneDensity_memLp T hT).integrable le_top)
  intro A hA _
  rw [positiveAdjointOneDensity_indicator S hS A hA,
    positiveAdjointOneDensity_indicator T hT A hA]
  exact integral_mono_ae (L1.integrable_coeFn _) (L1.integrable_coeFn _)
    ((Lp.coeFn_le _ _).mpr (hST _ (lOneIndicator_nonneg A hA)))

end ThesisCommon
