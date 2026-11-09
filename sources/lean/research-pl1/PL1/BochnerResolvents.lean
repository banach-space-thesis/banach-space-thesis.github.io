import PL1.NoiseSemigroup
import PL1.SeparableRange
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Bochner resolvent representation and operator-norm truncation -/

noncomputable section
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal

namespace PL1.Noise
open Walsh ExponentialTime

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

theorem noiseL1_apply_norm_le (u : ℝ≥0) (f : Lp 𝕜 1 haar) :
    ‖noiseL1 𝕜 rates u f‖ ≤ ‖f‖ :=
  ((noiseL1 𝕜 rates u).le_opNorm f).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norm_noiseL1_le_one 𝕜 rates u) (norm_nonneg f))

theorem integrable_noiseL1 (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (f : Lp 𝕜 1 haar) :
    Integrable (fun u => noiseL1 𝕜 rates u f) μ := by
  let := Walsh.separableSpace_scalarL1 𝕜
  exact Integrable.of_bound (continuous_noiseL1_apply 𝕜 rates f).aestronglyMeasurable ‖f‖
    (ae_of_all μ (fun u => noiseL1_apply_norm_le 𝕜 rates u f))

def averageNoiseLinear (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    Lp 𝕜 1 haar →ₗ[𝕜] Lp 𝕜 1 haar where
  toFun f := ∫ u, noiseL1 𝕜 rates u f ∂μ
  map_add' f g := by
    simp only [map_add]
    exact integral_add (integrable_noiseL1 𝕜 rates μ f) (integrable_noiseL1 𝕜 rates μ g)
  map_smul' c f := by
    simp only [map_smul, integral_smul, RingHom.id_apply]

theorem norm_averageNoiseLinear_le (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (f : Lp 𝕜 1 haar) :
    ‖averageNoiseLinear 𝕜 rates μ f‖ ≤ μ.real univ * ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (ae_of_all μ (fun u => noiseL1_apply_norm_le 𝕜 rates u f))
  exact h.trans_eq (mul_comm _ _)

def averageNoiseL1 (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar :=
  (averageNoiseLinear 𝕜 rates μ).mkContinuous (μ.real univ) (norm_averageNoiseLinear_le 𝕜 rates μ)

@[simp] theorem averageNoiseL1_apply (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (f : Lp 𝕜 1 haar) :
    averageNoiseL1 𝕜 rates μ f = ∫ u, noiseL1 𝕜 rates u f ∂μ := rfl

theorem norm_averageNoiseL1_le (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    ‖averageNoiseL1 𝕜 rates μ‖ ≤ μ.real univ :=
  ContinuousLinearMap.opNorm_le_bound _ (measureReal_nonneg) (norm_averageNoiseLinear_le 𝕜 rates μ)

theorem averageNoiseL1_timeMeasure (t : PositiveTime) :
    letI := isProbabilityMeasure_timeMeasure t.property
    averageNoiseL1 𝕜 rates (timeMeasure t) = resolventL1 𝕜 rates t := by
  let := isProbabilityMeasure_timeMeasure t.property
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [averageNoiseL1_apply, noiseL1_character, integral_smul_const,
    integral_laplace_ofReal t.property _ (rateSum_nonneg rates F), resolventL1_scalarCharacter]

/-- The actual convolution resolvent equals the Bochner average on every L1 input. -/
theorem resolventL1_eq_integral (t : PositiveTime) (f : Lp 𝕜 1 haar) :
    resolventL1 𝕜 rates t f = ∫ u, noiseL1 𝕜 rates u f ∂timeMeasure t := by
  let := isProbabilityMeasure_timeMeasure t.property
  exact (DFunLike.congr_fun (averageNoiseL1_timeMeasure 𝕜 rates t) f).symm

theorem averageNoiseL1_split (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (A : Set ℝ≥0) (hA : MeasurableSet A) :
    averageNoiseL1 𝕜 rates μ = averageNoiseL1 𝕜 rates (μ.restrict A) +
      averageNoiseL1 𝕜 rates (μ.restrict Aᶜ) := by
  ext f
  simp only [averageNoiseL1_apply, add_apply]
  rw [← integral_add_measure (integrable_noiseL1 𝕜 rates (μ.restrict A) f)
    (integrable_noiseL1 𝕜 rates (μ.restrict Aᶜ) f), Measure.restrict_add_restrict_compl hA]

theorem timeMeasure_real_Iic (t : PositiveTime) (ε : ℝ≥0) :
    (timeMeasure t).real (Iic ε) = 1 - Real.exp (-(ε : ℝ) / (t : ℝ)) := by
  let := isProbabilityMeasure_expMeasure (inv_pos.mpr t.property)
  rw [measureReal_def, timeMeasure,
    Measure.map_apply measurable_real_toNNReal measurableSet_Iic]
  have hp : Real.toNNReal ⁻¹' Iic ε = Iic (ε : ℝ) := by
    ext x
    exact Real.toNNReal_le_iff_le_coe
  rw [hp, ← measureReal_def, ← cdf_eq_real,
    cdf_expMeasure_eq (inv_pos.mpr t.property), ite_eq_left ε.coe_nonneg]
  congr 2
  ring

/-- The same noise average with times below ε omitted. -/
def truncatedResolventL1 (t : PositiveTime) (ε : ℝ≥0) :
    Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar := by
  let := isProbabilityMeasure_timeMeasure t.property
  exact averageNoiseL1 𝕜 rates ((timeMeasure t).restrict (Ici ε))

theorem norm_resolventL1_sub_truncated_le (t : PositiveTime) (ε : ℝ≥0) :
    ‖resolventL1 𝕜 rates t - truncatedResolventL1 𝕜 rates t ε‖ ≤
      1 - Real.exp (-(ε : ℝ) / (t : ℝ)) := by
  let := isProbabilityMeasure_timeMeasure t.property
  have hs := averageNoiseL1_split 𝕜 rates (timeMeasure t) (Ici ε) measurableSet_Ici
  rw [averageNoiseL1_timeMeasure] at hs
  have he : resolventL1 𝕜 rates t - truncatedResolventL1 𝕜 rates t ε =
      averageNoiseL1 𝕜 rates ((timeMeasure t).restrict (Iio ε)) := by
    rw [hs]
    change averageNoiseL1 𝕜 rates ((timeMeasure t).restrict (Ici ε)) +
      averageNoiseL1 𝕜 rates ((timeMeasure t).restrict (Ici ε)ᶜ) -
      averageNoiseL1 𝕜 rates ((timeMeasure t).restrict (Ici ε)) = _
    rw [add_sub_cancel_left, compl_Ici]
  rw [he]
  apply (norm_averageNoiseL1_le 𝕜 rates ((timeMeasure t).restrict (Iio ε))).trans
  rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [← timeMeasure_real_Iic t ε]
  exact measureReal_mono Iio_subset_Iic_self

theorem truncatedResolventL1_apply (t : PositiveTime) (ε : ℝ≥0) (f : Lp 𝕜 1 haar) :
    truncatedResolventL1 𝕜 rates t ε f =
      ∫ u in Ici ε, noiseL1 𝕜 rates u f ∂timeMeasure t := rfl

/-- The truncated averages converge in actual L1 operator norm, for any
nonnegative cutoffs tending to zero. -/
theorem truncatedResolventL1_tendsto {α : Type*} (l : Filter α)
    (t : PositiveTime) (ε : α → ℝ≥0) (hε : Tendsto (fun a => (ε a : ℝ)) l (𝓝 0)) :
    Tendsto (fun a => truncatedResolventL1 𝕜 rates t (ε a)) l (𝓝 (resolventL1 𝕜 rates t)) := by
  have hb : Tendsto (fun a => 1 - Real.exp (-(ε a : ℝ) / (t : ℝ))) l (𝓝 (0 : ℝ)) := by
    have he := (Real.continuous_exp.tendsto (-(0 : ℝ) / (t : ℝ))).comp
      (hε.neg.div_const (t : ℝ))
    simpa only [neg_zero, zero_div, Real.exp_zero, sub_self, Function.comp_def] using
      (tendsto_const_nhds (x := (1 : ℝ)) (f := l)).sub he
  have hn : Tendsto (fun a => ‖truncatedResolventL1 𝕜 rates t (ε a) -
      resolventL1 𝕜 rates t‖) l (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun a => by
      rw [norm_sub_rev]
      exact norm_resolventL1_sub_truncated_le 𝕜 rates t (ε a)) hb
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end PL1.Noise
