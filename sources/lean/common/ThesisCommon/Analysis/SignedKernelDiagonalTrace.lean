import ThesisCommon.Analysis.KernelDiagonalLocalization
import ThesisCommon.Analysis.SignedKernelIntegration

/-! Measurable diagonal atoms of genuine signed reverse kernels of real L1
operators. In particular, the diagonal coefficients of complementary operators
sum to one almost everywhere. The kernels represent all bounded operators. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon

private theorem real_add_finite {Y : Type*} [MeasurableSpace Y]
    (ρ σ : Measure Y) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] (s : Set Y) :
    (ρ + σ).real s = ρ.real s + σ.real s := measureReal_add_apply

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

def SignedReverseKernel.diagonal (K : SignedReverseKernel X X) (x : X) : ℝ := K.fibre x {x}

omit [SecondCountableTopology X] in
theorem SignedReverseKernel.diagonal_eq (K : SignedReverseKernel X X) (x : X) :
    K.diagonal x = (K.posPart x).real {x} - (K.negPart x).real {x} :=
  Measure.toSignedMeasure_sub_apply (measurableSet_singleton x)

theorem SignedReverseKernel.diagonal_measurable (K : SignedReverseKernel X X) :
    Measurable K.diagonal := by
  have he : K.diagonal = fun x => (K.posPart x).real {x} - (K.negPart x).real {x} :=
    funext K.diagonal_eq
  rw [he]
  exact (measurable_kernel_diagonal K.posPart).ennreal_toReal.sub
    (measurable_kernel_diagonal K.negPart).ennreal_toReal

omit [SecondCountableTopology X] in
theorem SignedReverseKernel.abs_diagonal_le (K : SignedReverseKernel X X) (x : X) :
    |K.diagonal x| ≤ (K.variationKernel x).real univ := by
  rw [K.diagonal_eq, SignedReverseKernel.variationKernel, Kernel.add_apply,
    measureReal_add_apply]
  have hp := measureReal_mono (μ := K.posPart x) (subset_univ ({x} : Set X))
  have hn := measureReal_mono (μ := K.negPart x) (subset_univ ({x} : Set X))
  have hp0 : 0 ≤ (K.posPart x).real {x} := measureReal_nonneg
  have hn0 : 0 ≤ (K.negPart x).real {x} := measureReal_nonneg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {μ : Measure X} [IsFiniteMeasure μ]
  [CompactSpace X] [TotallyDisconnectedSpace X] [StandardBorelSpace X]

def realL1ReverseKernel (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) : SignedReverseKernel X X :=
  (exists_signedOperatorReverseKernel T).choose

theorem realL1ReverseKernel_spec (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) :
    (∀ x, ((realL1ReverseKernel T).fibre x).totalVariation univ ≤ ENNReal.ofReal ‖T‖) ∧
    μ ⊗ₘ (realL1ReverseKernel T).posPart = clopenOperatorMeasure T⁺ (posPart_nonneg T) ∧
    μ ⊗ₘ (realL1ReverseKernel T).negPart = clopenOperatorMeasure T⁻ (negPart_nonneg T) ∧
    μ ⊗ₘ (realL1ReverseKernel T).variationKernel = clopenOperatorMeasure |T| (abs_nonneg T) :=
  (exists_signedOperatorReverseKernel T).choose_spec

def realL1Diagonal (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) : X → ℝ :=
  (realL1ReverseKernel T).diagonal

theorem realL1Diagonal_measurable (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) :
    Measurable (realL1Diagonal T) := (realL1ReverseKernel T).diagonal_measurable

theorem realL1Diagonal_abs_le (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (x : X) :
    |realL1Diagonal T x| ≤ ‖T‖ := by
  apply ((realL1ReverseKernel T).abs_diagonal_le x).trans
  have h := (realL1ReverseKernel_spec T).1 x
  rw [(realL1ReverseKernel T).fibre_totalVariation] at h
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal (norm_nonneg T))

omit [StandardBorelSpace X] in
theorem clopenOperatorMeasure_id_compProd :
    clopenOperatorMeasure (ContinuousLinearMap.id ℝ (Lp ℝ 1 μ)) (fun _ hf => hf) =
      μ ⊗ₘ (Kernel.id : Kernel X X) := by
  apply Measure.ext_prod
  intro a b ha hb
  rw [clopenOperatorMeasure_prod _ _ ha hb, Measure.compProd_id,
    Measure.map_apply (show Measurable (fun x : X => (x, x)) from
      measurable_id.prodMk measurable_id) (ha.prod hb)]
  change ENNReal.ofReal (∫ y in b, lOneIndicator μ a ha y ∂μ) = _
  rw [integral_congr_ae (ae_restrict_of_ae (lOneIndicator_coe a ha)),
    setIntegral_indicator ha, integral_const]
  simp only [Measure.restrict_apply_univ, smul_eq_mul, mul_one, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top μ _)]
  congr 1
  ext x
  simp [and_comm]

theorem realL1ReverseKernel_complement_balance
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) :
    ∀ᵐ x ∂μ, (realL1ReverseKernel T).posPart x +
        (realL1ReverseKernel (ContinuousLinearMap.id ℝ (Lp ℝ 1 μ) - T)).posPart x =
      Measure.dirac x + ((realL1ReverseKernel T).negPart x +
        (realL1ReverseKernel (ContinuousLinearMap.id ℝ (Lp ℝ 1 μ) - T)).negPart x) := by
  change (fun x => ((realL1ReverseKernel T).posPart +
      (realL1ReverseKernel (ContinuousLinearMap.id ℝ (Lp ℝ 1 μ) - T)).posPart : Kernel X X) x) =ᵐ[μ]
    (fun x => (Kernel.id + ((realL1ReverseKernel T).negPart +
      (realL1ReverseKernel (ContinuousLinearMap.id ℝ (Lp ℝ 1 μ) - T)).negPart) : Kernel X X) x)
  apply Kernel.ae_eq_of_compProd_eq
  simp only [Measure.compProd_add_right]
  rw [(realL1ReverseKernel_spec T).2.1, (realL1ReverseKernel_spec T).2.2.1,
    (realL1ReverseKernel_spec (ContinuousLinearMap.id ℝ _ - T)).2.1,
    (realL1ReverseKernel_spec (ContinuousLinearMap.id ℝ _ - T)).2.2.1,
    ← clopenOperatorMeasure_id_compProd]
  have h := signedOperatorMeasure_add T (ContinuousLinearMap.id ℝ _ - T)
  rw [add_sub_cancel, signedOperatorMeasure_nonneg _ (fun _ hf => hf),
    signedOperatorMeasure_def, signedOperatorMeasure_def] at h
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hv := congrArg (fun m : SignedMeasure (X × X) => m s) h
  simp only [VectorMeasure.add_apply, VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable hs] at hv
  simp only [← measureReal_def, real_add_finite]
  linarith

theorem realL1Diagonal_add_complement (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) :
    ∀ᵐ x ∂μ, realL1Diagonal T x + realL1Diagonal (ContinuousLinearMap.id ℝ _ - T) x = 1 := by
  filter_upwards [realL1ReverseKernel_complement_balance T] with x hx
  have he := congrArg (fun m : Measure X => m {x}) hx
  simp only [Measure.add_apply] at he
  have hd : (Measure.dirac x) {x} = 1 := by simp
  rw [hd] at he
  have hreal := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
    ENNReal.toReal_one] at hreal
  simp only [realL1Diagonal, SignedReverseKernel.diagonal_eq, measureReal_def]
  linarith

end ThesisCommon
