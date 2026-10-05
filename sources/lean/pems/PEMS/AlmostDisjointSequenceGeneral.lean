import PEMS.FiniteMeasureWitnessReduction
import PEMS.DisjointOutputWitnessWeis
import PEMS.FiniteAlmostDisjointSequence
import ThesisCommon.Analysis.L1IsometryDisjointness

/-! Source Lemma 5.5 in its full real and complex L1 scope. The finite
operator model carries actual isometric embeddings, so disjointness and
norm-null errors transport back to the original spaces. -/
noncomputable section
open MeasureTheory Filter Set Topology Function ThesisCommon
namespace PEMS
variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

structure FiniteL1OperatorModel (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) where
  input : Measure X
  output : Measure Y
  finiteInput : IsFiniteMeasure input
  finiteOutput : IsFiniteMeasure output
  domainEmbed : LOne 𝕜 input →ₗᵢ[𝕜] LOne 𝕜 μ
  rangeEmbed : LOne 𝕜 output →ₗᵢ[𝕜] LOne 𝕜 ν
  operator : LOne 𝕜 input →L[𝕜] LOne 𝕜 output
  factor : ∀ x, rangeEmbed (operator x) = T (domainEmbed x)
  weakNorm : weakEssentialNorm operator = weakEssentialNorm T

theorem exists_finiteL1OperatorModel_of_witness
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (f : ℕ → LOne 𝕜 μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) {c : ℝ} (hw : weakEssentialNorm T ≤ c)
    (hc : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 c))
    (hRange : ∀ (ρ : Measure X), IsFiniteMeasure ρ →
      ∀ J : LOne 𝕜 ρ →ₗᵢ[𝕜] LOne 𝕜 μ,
        Nonempty (FiniteL1RangeFactor (T.comp J.toContinuousLinearMap)))
    (hFormula : ∀ (ρ : Measure X) (η : Measure Y), IsFiniteMeasure ρ → IsFiniteMeasure η →
      ∀ R : LOne 𝕜 ρ →L[𝕜] LOne 𝕜 η,
        weakEssentialNorm R = localizedWeakNoncompactness R) :
    Nonempty (FiniteL1OperatorModel T) := by
  obtain ⟨ρ, hρ, J, v, hv⟩ := exists_finite_lOne_isometric_sequence_envelope f
  letI := hρ
  obtain ⟨K⟩ := hRange ρ hρ J
  letI := K.finite
  let R := K.retract.comp (T.comp J.toContinuousLinearMap)
  have hfactor (x : LOne 𝕜 ρ) : K.embed (R x) = T (J x) :=
    DFunLike.congr_fun K.factor x
  have hvnorm (n : ℕ) : ‖v n‖ ≤ 1 := by
    calc
      ‖v n‖ = ‖J (v n)‖ := (J.norm_map _).symm
      _ = ‖f n‖ := by rw [hv]
      _ ≤ 1 := hf n
  have hcut (n : ℕ) : ‖lpCut (A n) (hA n) (R (v n))‖ =
      ‖lpCut (A n) (hA n) (T (f n))‖ := by
    calc
      _ = ‖K.embed (lpCut (A n) (hA n) (R (v n)))‖ := (K.embed.norm_map _).symm
      _ = _ := by rw [K.commute_cut, hfactor, hv]
  have hc' : Tendsto (fun n => ‖lpCut (A n) (hA n) (R (v n))‖) atTop (𝓝 c) := by
    simpa only [hcut] using hc
  have hloc : c ≤ localizedWeakNoncompactness R := by
    rw [localizedWeakNoncompactness_eq_alphaTheta_univ]
    exact cutoff_norm_limit_le_alphaTheta_univ R v hvnorm A hA
      (measure_disjoint_sequence_tendsto_zero A hA hd) hc'
  have hle : weakEssentialNorm R ≤ weakEssentialNorm T := by
    calc
      weakEssentialNorm R ≤ ‖K.retract‖ * weakEssentialNorm (T.comp J.toContinuousLinearMap) :=
        weakEssentialNorm_comp_left_le _ _
      _ ≤ weakEssentialNorm (T.comp J.toContinuousLinearMap) :=
        mul_le_of_le_one_left (weakEssentialNorm_nonneg _) K.norm_retract_le
      _ ≤ weakEssentialNorm T * ‖J.toContinuousLinearMap‖ := weakEssentialNorm_comp_right_le _ _
      _ ≤ weakEssentialNorm T := mul_le_of_le_one_right (weakEssentialNorm_nonneg _)
        J.norm_toContinuousLinearMap_le
  refine ⟨⟨ρ, K.measure, hρ, K.finite, J, K.embed, R, hfactor, le_antisymm hle ?_⟩⟩
  exact (hw.trans hloc).trans_eq (hFormula ρ K.measure hρ K.finite R).symm

theorem exists_real_finiteL1OperatorModel (hμ : StrictlyLocalizable μ)
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : ¬IsWeaklyCompactOperator T) :
    Nonempty (FiniteL1OperatorModel T) := by
  obtain ⟨f, A, hA, c, hf, _, hd, hw, hc⟩ :=
    exists_real_disjointOutputWitness_weakEssentialNorm hμ T hT
  apply exists_finiteL1OperatorModel_of_witness T f (fun n => (hf n).le) A hA hd hw hc
  · intro ρ hρ J
    letI := hρ
    exact exists_finiteL1RangeFactor_real _
  · intro ρ η hρ hη R
    letI := hρ
    letI := hη
    exact weakEssentialNorm_eq_localized_real_finite R

theorem lemma_5_5_real (hμ : StrictlyLocalizable μ)
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : ¬IsWeaklyCompactOperator T) :
    ∃ (u : ℕ → LOne ℝ μ) (q : ℕ → LOne ℝ ν),
      (Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0) ∧
      (Pairwise fun i j => ∀ᵐ y ∂ν, q i y = 0 ∨ q j y = 0) ∧
      (∀ n, ‖u n‖ = 1) ∧
      Tendsto (fun n => ‖T (u n) - q n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖T (u n)‖) atTop (𝓝 (weakEssentialNorm T)) := by
  obtain ⟨M⟩ := exists_real_finiteL1OperatorModel hμ T hT
  letI := M.finiteInput
  letI := M.finiteOutput
  have hR : ¬IsWeaklyCompactOperator M.operator := by
    intro h
    exact hT ((weakEssentialNorm_eq_zero_iff T).mp
      (M.weakNorm.symm.trans h.weakEssentialNorm_eq_zero))
  obtain ⟨u, q, hdu, hdq, hu, herr, hnorm⟩ := lemma_5_4_real_finite M.operator hR
  refine ⟨M.domainEmbed ∘ u, M.rangeEmbed ∘ q,
    (fun i j hij => lOne_isometry_preserves_ae_disjoint M.domainEmbed _ _ (hdu hij)),
    (fun i j hij => lOne_isometry_preserves_ae_disjoint M.rangeEmbed _ _ (hdq hij)),
    (fun n => (M.domainEmbed.norm_map _).trans (hu n)), ?_, ?_⟩
  · have he (n : ℕ) : ‖T (M.domainEmbed (u n)) - M.rangeEmbed (q n)‖ =
        ‖M.operator (u n) - q n‖ := by
      rw [← M.factor, ← map_sub, M.rangeEmbed.norm_map]
    simpa only [Function.comp_apply, he] using herr
  · have he (n : ℕ) : ‖T (M.domainEmbed (u n))‖ = ‖M.operator (u n)‖ := by
      rw [← M.factor, M.rangeEmbed.norm_map]
    simpa only [Function.comp_apply, he, M.weakNorm] using hnorm

theorem exists_complex_finiteL1OperatorModel (hμ : StrictlyLocalizable μ)
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) (hT : ¬IsWeaklyCompactOperator T) :
    Nonempty (FiniteL1OperatorModel T) := by
  obtain ⟨f, A, hA, c, hf, _, hd, hw, hc⟩ :=
    exists_complex_disjointOutputWitness_weakEssentialNorm hμ T hT
  apply exists_finiteL1OperatorModel_of_witness T f (fun n => (hf n).le) A hA hd hw hc
  · intro ρ hρ J
    letI := hρ
    exact exists_finiteL1RangeFactor_complex _
  · intro ρ η hρ hη R
    letI := hρ
    letI := hη
    exact weakEssentialNorm_eq_localized_complex_finite R

theorem lemma_5_5_complex (hμ : StrictlyLocalizable μ)
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) (hT : ¬IsWeaklyCompactOperator T) :
    ∃ (u : ℕ → LOne ℂ μ) (q : ℕ → LOne ℂ ν),
      (Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0) ∧
      (Pairwise fun i j => ∀ᵐ y ∂ν, q i y = 0 ∨ q j y = 0) ∧
      (∀ n, ‖u n‖ = 1) ∧
      Tendsto (fun n => ‖T (u n) - q n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖T (u n)‖) atTop (𝓝 (weakEssentialNorm T)) := by
  obtain ⟨M⟩ := exists_complex_finiteL1OperatorModel hμ T hT
  letI := M.finiteInput
  letI := M.finiteOutput
  have hR : ¬IsWeaklyCompactOperator M.operator := by
    intro h
    exact hT ((weakEssentialNorm_eq_zero_iff T).mp
      (M.weakNorm.symm.trans h.weakEssentialNorm_eq_zero))
  obtain ⟨u, q, hdu, hdq, hu, herr, hnorm⟩ := lemma_5_4_complex_finite M.operator hR
  refine ⟨M.domainEmbed ∘ u, M.rangeEmbed ∘ q,
    (fun i j hij => lOne_isometry_preserves_ae_disjoint M.domainEmbed _ _ (hdu hij)),
    (fun i j hij => lOne_isometry_preserves_ae_disjoint M.rangeEmbed _ _ (hdq hij)),
    (fun n => (M.domainEmbed.norm_map _).trans (hu n)), ?_, ?_⟩
  · have he (n : ℕ) : ‖T (M.domainEmbed (u n)) - M.rangeEmbed (q n)‖ =
        ‖M.operator (u n) - q n‖ := by
      rw [← M.factor, ← map_sub, M.rangeEmbed.norm_map]
    simpa only [Function.comp_apply, he] using herr
  · have he (n : ℕ) : ‖T (M.domainEmbed (u n))‖ = ‖M.operator (u n)‖ := by
      rw [← M.factor, M.rangeEmbed.norm_map]
    simpa only [Function.comp_apply, he, M.weakNorm] using hnorm

end PEMS
