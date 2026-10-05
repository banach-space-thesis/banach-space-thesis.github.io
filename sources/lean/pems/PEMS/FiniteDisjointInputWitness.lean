import PEMS.FiniteDisjointExtremal
import PEMS.ExtremalSplittingNormalization
import PEMS.ComplexFiniteWeisBestApproximation
import ThesisCommon.Analysis.L1SubsequenceSplitting
import ThesisCommon.Analysis.L1WeakSequenceUniformIntegrable

/-! The input-disjoint stage of source Lemma 5.4 on arbitrary finite measure
spaces. The splitting, normalization and residual uniform integrability are
all proved for actual L1 vectors and the original operator. -/
noncomputable section
open MeasureTheory Set Filter Topology Function ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem exists_real_finite_disjointInput_extremal
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : ¬IsWeaklyCompactOperator T) :
    ∃ u : ℕ → LOne ℝ μ, ∃ B : ℕ → Set Y, ∃ hB : ∀ n, MeasurableSet (B n),
      (∀ n, ‖u n‖ = 1) ∧
      (Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0) ∧
      Pairwise (Disjoint on B) ∧
      Tendsto (fun n => ‖lpCut (B n) (hB n) (T (u n))‖) atTop
        (𝓝 (weakEssentialNorm T)) ∧
      UniformIntegrable (fun n => (lpCut (B n)ᶜ (hB n).compl (T (u n)) : Y → ℝ)) 1 ν := by
  have hw : 0 < weakEssentialNorm T := lt_of_le_of_ne (weakEssentialNorm_nonneg T)
    (Ne.symm fun heq => hT ((weakEssentialNorm_eq_zero_iff T).mp heq))
  have hc : 0 < localizedWeakNoncompactness T :=
    (weakEssentialNorm_eq_localized_real_finite T) ▸ hw
  obtain ⟨f, A, hA, hf, hAd, hconv⟩ := exists_disjointOutputWitness_extremal T hc
  obtain ⟨r, g, h, x, hr, hfg, _, hhd, hgw, _, hh⟩ :=
    exists_real_lOne_subsequence_splitting f (fun n => (hf n).le)
  have hTgw : Tendsto (fun n => toWeakSpace ℝ (LOne ℝ ν) (T (g n))) atTop
      (𝓝 (toWeakSpace ℝ (LOne ℝ ν) (T x))) :=
    ((WeakSpace.map T).continuous.tendsto _).comp hgw
  have hgUI := unifIntegrable_of_real_lOne_weak_tendsto (fun n => T (g n)) hTgw
  have hAr : Pairwise (Disjoint on (A ∘ r)) := fun i j hij => hAd (hr.injective.ne hij)
  have hmass := measure_disjoint_sequence_tendsto_zero (A ∘ r) (fun n => hA _) hAr (μ := ν)
  have hc' : 0 < alphaTheta T univ := by
    simpa only [localizedWeakNoncompactness_eq_alphaTheta_univ] using hc
  have hconv' : Tendsto (fun n => ‖lpCut (A (r n)) (hA _) (T (f (r n)))‖) atTop
      (𝓝 (alphaTheta T univ)) := by
    simpa only [Function.comp_def, localizedWeakNoncompactness_eq_alphaTheta_univ] using
      hconv.comp hr.tendsto_atTop
  obtain ⟨u, B, hB, hu, hd, hBd, _, hlim, hUI⟩ :=
    exists_normalized_disjoint_extremal_of_splitting T (f ∘ r) g h hfg
      (fun n => (hh n).trans (hf _).le) hhd (A ∘ r) (fun n => hA _) hAr hmass hgUI hc' hconv'
  refine ⟨u, B, hB, hu, hd, hBd, ?_, hUI⟩
  simpa only [weakEssentialNorm_eq_localized_real_finite,
    localizedWeakNoncompactness_eq_alphaTheta_univ] using hlim

theorem exists_complex_finite_disjointInput_extremal
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) (hT : ¬IsWeaklyCompactOperator T) :
    ∃ u : ℕ → LOne ℂ μ, ∃ B : ℕ → Set Y, ∃ hB : ∀ n, MeasurableSet (B n),
      (∀ n, ‖u n‖ = 1) ∧
      (Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0) ∧
      Pairwise (Disjoint on B) ∧
      Tendsto (fun n => ‖lpCut (B n) (hB n) (T (u n))‖) atTop
        (𝓝 (weakEssentialNorm T)) ∧
      UniformIntegrable (fun n => (lpCut (B n)ᶜ (hB n).compl (T (u n)) : Y → ℂ)) 1 ν := by
  have hw : 0 < weakEssentialNorm T := lt_of_le_of_ne (weakEssentialNorm_nonneg T)
    (Ne.symm fun heq => hT ((weakEssentialNorm_eq_zero_iff T).mp heq))
  have hc : 0 < localizedWeakNoncompactness T :=
    (weakEssentialNorm_eq_localized_complex_finite T) ▸ hw
  obtain ⟨f, A, hA, hf, hAd, hconv⟩ := exists_disjointOutputWitness_extremal T hc
  obtain ⟨r, g, h, x, hr, hfg, _, hhd, hgw, _, hh⟩ :=
    exists_complex_lOne_subsequence_splitting f (fun n => (hf n).le)
  have hTgw : Tendsto (fun n => toWeakSpace ℂ (LOne ℂ ν) (T (g n))) atTop
      (𝓝 (toWeakSpace ℂ (LOne ℂ ν) (T x))) :=
    ((WeakSpace.map T).continuous.tendsto _).comp hgw
  have hgUI := unifIntegrable_of_complex_lOne_weak_tendsto (fun n => T (g n)) hTgw
  have hAr : Pairwise (Disjoint on (A ∘ r)) := fun i j hij => hAd (hr.injective.ne hij)
  have hmass := measure_disjoint_sequence_tendsto_zero (A ∘ r) (fun n => hA _) hAr (μ := ν)
  have hc' : 0 < alphaTheta T univ := by
    simpa only [localizedWeakNoncompactness_eq_alphaTheta_univ] using hc
  have hconv' : Tendsto (fun n => ‖lpCut (A (r n)) (hA _) (T (f (r n)))‖) atTop
      (𝓝 (alphaTheta T univ)) := by
    simpa only [Function.comp_def, localizedWeakNoncompactness_eq_alphaTheta_univ] using
      hconv.comp hr.tendsto_atTop
  obtain ⟨u, B, hB, hu, hd, hBd, _, hlim, hUI⟩ :=
    exists_normalized_disjoint_extremal_of_splitting T (f ∘ r) g h hfg
      (fun n => (hh n).trans (hf _).le) hhd (A ∘ r) (fun n => hA _) hAr hmass hgUI hc' hconv'
  refine ⟨u, B, hB, hu, hd, hBd, ?_, hUI⟩
  simpa only [weakEssentialNorm_eq_localized_complex_finite,
    localizedWeakNoncompactness_eq_alphaTheta_univ] using hlim

end PEMS
