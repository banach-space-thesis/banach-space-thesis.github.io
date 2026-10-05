import ThesisCommon.Analysis.L1SequenceFiniteEnvelope
import ThesisCommon.Analysis.L1FiniteRangeFactor
import PEMS.ExtremalCutoffNorm
import PEMS.FactorizationSupContractions

/-! Countable disjoint-cut witnesses reduce to actual finite input and output
measures. The density and support maps preserve every output cut exactly;
contractivity controls both the weak essential norm and factorization supremum. -/
noncomputable section
open MeasureTheory Filter Set Topology Function ThesisCommon
namespace PEMS
variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_finite_measure_witness_reduction
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (f : ℕ → LOne 𝕜 μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) {c : ℝ}
    (hc : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 c))
    (hRange : ∀ (ρ : Measure X), IsFiniteMeasure ρ →
      ∀ J : LOne 𝕜 ρ →ₗᵢ[𝕜] LOne 𝕜 μ,
        Nonempty (FiniteL1RangeFactor (T.comp J.toContinuousLinearMap))) :
    ∃ ρ : Measure X, IsFiniteMeasure ρ ∧ ∃ η : Measure Y, IsFiniteMeasure η ∧
      ∃ R : LOne 𝕜 ρ →L[𝕜] LOne 𝕜 η,
        c ≤ localizedWeakNoncompactness R ∧
        weakEssentialNorm R ≤ weakEssentialNorm T ∧
        factorizationSup (EllOne 𝕜) R ≤ factorizationSup (EllOne 𝕜) T := by
  obtain ⟨ρ, hρ, J, v, hv⟩ := exists_finite_lOne_isometric_sequence_envelope f
  letI := hρ
  obtain ⟨K⟩ := hRange ρ hρ J
  letI := K.finite
  let R := K.retract.comp (T.comp J.toContinuousLinearMap)
  have hfactor (n : ℕ) : K.embed (R (v n)) = T (f n) := by
    have hh := congrArg (fun S => S (v n)) K.factor
    change K.embed (R (v n)) = T (J (v n)) at hh
    simpa only [hv] using hh
  have hvnorm (n : ℕ) : ‖v n‖ ≤ 1 := by
    calc
      ‖v n‖ = ‖J (v n)‖ := (J.norm_map _).symm
      _ = ‖f n‖ := by rw [hv]
      _ ≤ 1 := hf n
  have hcut (n : ℕ) : ‖lpCut (A n) (hA n) (R (v n))‖ =
      ‖lpCut (A n) (hA n) (T (f n))‖ := by
    calc
      _ = ‖K.embed (lpCut (A n) (hA n) (R (v n)))‖ := (K.embed.norm_map _).symm
      _ = _ := by rw [K.commute_cut, hfactor]
  have hc' : Tendsto (fun n => ‖lpCut (A n) (hA n) (R (v n))‖) atTop (𝓝 c) := by
    simpa only [hcut] using hc
  refine ⟨ρ, hρ, K.measure, K.finite, R, ?_, ?_, ?_⟩
  · rw [localizedWeakNoncompactness_eq_alphaTheta_univ]
    exact cutoff_norm_limit_le_alphaTheta_univ R v hvnorm A hA
      (measure_disjoint_sequence_tendsto_zero A hA hd) hc'
  · calc
      weakEssentialNorm R ≤ ‖K.retract‖ * weakEssentialNorm (T.comp J.toContinuousLinearMap) :=
        weakEssentialNorm_comp_left_le _ _
      _ ≤ weakEssentialNorm (T.comp J.toContinuousLinearMap) :=
        mul_le_of_le_one_left (weakEssentialNorm_nonneg _) K.norm_retract_le
      _ ≤ weakEssentialNorm T * ‖J.toContinuousLinearMap‖ :=
        weakEssentialNorm_comp_right_le _ _
      _ ≤ weakEssentialNorm T := mul_le_of_le_one_right (weakEssentialNorm_nonneg _)
        J.norm_toContinuousLinearMap_le
  · exact factorizationSup_ellOne_of_contractive_composition_le T K.retract
      J.toContinuousLinearMap K.norm_retract_le J.norm_toContinuousLinearMap_le

theorem exists_real_finite_measure_witness_reduction
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (f : ℕ → LOne ℝ μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) {c : ℝ}
    (hc : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 c)) :
    ∃ ρ : Measure X, IsFiniteMeasure ρ ∧ ∃ η : Measure Y, IsFiniteMeasure η ∧
      ∃ R : LOne ℝ ρ →L[ℝ] LOne ℝ η,
        c ≤ localizedWeakNoncompactness R ∧
        weakEssentialNorm R ≤ weakEssentialNorm T ∧
        factorizationSup (EllOne ℝ) R ≤ factorizationSup (EllOne ℝ) T := by
  apply exists_finite_measure_witness_reduction T f hf A hA hd hc
  intro ρ hρ J
  letI := hρ
  exact exists_finiteL1RangeFactor_real _

theorem exists_complex_finite_measure_witness_reduction
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) (f : ℕ → LOne ℂ μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) {c : ℝ}
    (hc : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 c)) :
    ∃ ρ : Measure X, IsFiniteMeasure ρ ∧ ∃ η : Measure Y, IsFiniteMeasure η ∧
      ∃ R : LOne ℂ ρ →L[ℂ] LOne ℂ η,
        c ≤ localizedWeakNoncompactness R ∧
        weakEssentialNorm R ≤ weakEssentialNorm T ∧
        factorizationSup (EllOne ℂ) R ≤ factorizationSup (EllOne ℂ) T := by
  apply exists_finite_measure_witness_reduction T f hf A hA hd hc
  intro ρ hρ J
  letI := hρ
  exact exists_finiteL1RangeFactor_complex _

end PEMS
