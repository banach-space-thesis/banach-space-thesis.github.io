import ThesisCommon.Analysis.SequenceSpaces

/-! Multiplication of a finite positive measure by a scalar changes `Lp` by
an explicitly normalized linear isometry. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

theorem lebesgueLp_mem_of_smul_measure {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ∞)
    (f : Lp E p (c • μ)) : MemLp f p μ := by
  have h := (Lp.memLp f).smul_measure (c := c⁻¹) (ENNReal.inv_ne_top.mpr hc)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc hc', one_smul] using h

def lebesgueLpMeasureScaleValue (c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ∞)
    (f : Lp E p (c • μ)) : Lp E p μ :=
  ((c.toReal ^ (1 / p.toReal) : ℝ) : 𝕜) •
    (lebesgueLp_mem_of_smul_measure hc hc' f).toLp f

theorem lebesgueLpMeasureScaleValue_coe (c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ∞)
    (f : Lp E p (c • μ)) :
    lebesgueLpMeasureScaleValue (𝕜 := 𝕜) (μ := μ) c hc hc' f =ᵐ[μ]
      fun x => ((c.toReal ^ (1 / p.toReal) : ℝ) : 𝕜) • f x := by
  unfold lebesgueLpMeasureScaleValue
  exact (Lp.coeFn_smul _ _).trans
    ((MemLp.coeFn_toLp (lebesgueLp_mem_of_smul_measure hc hc' f)).const_smul _)

theorem lebesgueLpMeasureScaleValue_norm (hp : p ≠ ∞)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ∞) (f : Lp E p (c • μ)) :
    ‖lebesgueLpMeasureScaleValue (𝕜 := 𝕜) (μ := μ) c hc hc' f‖ = ‖f‖ := by
  unfold lebesgueLpMeasureScaleValue
  rw [norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _), Lp.norm_toLp,
    Lp.norm_def, eLpNorm_smul_measure_of_ne_top hp, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_rpow]
  simp only [one_div, ENNReal.toReal_inv]

def lebesgueLpMeasureScale (hp : p ≠ ∞)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ∞) :
    Lp E p (c • μ) →ₗᵢ[𝕜] Lp E p μ where
  toFun := lebesgueLpMeasureScaleValue (𝕜 := 𝕜) (μ := μ) c hc hc'
  map_add' f g := by
    apply Lp.ext
    have hadd := (Measure.ae_smul_measure_iff hc).mp (Lp.coeFn_add f g)
    filter_upwards [lebesgueLpMeasureScaleValue_coe (𝕜 := 𝕜) c hc hc' (f + g),
      lebesgueLpMeasureScaleValue_coe (𝕜 := 𝕜) c hc hc' f,
      lebesgueLpMeasureScaleValue_coe (𝕜 := 𝕜) c hc hc' g,
      Lp.coeFn_add (lebesgueLpMeasureScaleValue (𝕜 := 𝕜) c hc hc' f)
        (lebesgueLpMeasureScaleValue (𝕜 := 𝕜) c hc hc' g), hadd]
      with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₄ h₅
    rw [h₁, h₄, h₂, h₃, h₅, smul_add]
  map_smul' a f := by
    apply Lp.ext
    have hsmul := (Measure.ae_smul_measure_iff hc).mp (Lp.coeFn_smul a f)
    filter_upwards [lebesgueLpMeasureScaleValue_coe (𝕜 := 𝕜) c hc hc' (a • f),
      lebesgueLpMeasureScaleValue_coe (𝕜 := 𝕜) c hc hc' f,
      Lp.coeFn_smul a (lebesgueLpMeasureScaleValue (𝕜 := 𝕜) c hc hc' f), hsmul]
      with x h₁ h₂ h₃ h₄
    simp only [RingHom.id_apply, Pi.smul_apply] at *
    rw [h₁, h₃, h₂, h₄, smul_comm]
  norm_map' := lebesgueLpMeasureScaleValue_norm hp c hc hc'

theorem lebesgueLpMeasureScale_surjective (hp : p ≠ ∞)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ∞) :
    Function.Surjective (lebesgueLpMeasureScale (𝕜 := 𝕜) (E := E) (μ := μ) hp c hc hc') := by
  intro g
  let a : 𝕜 := ((c.toReal ^ (1 / p.toReal) : ℝ) : 𝕜)
  have ha : a ≠ 0 := by
    apply RCLike.ofReal_ne_zero.mpr
    exact (Real.rpow_pos_of_pos (ENNReal.toReal_pos hc hc') _).ne'
  let f : Lp E p (c • μ) := ((Lp.memLp (a⁻¹ • g)).smul_measure hc').toLp ((a⁻¹ • g : Lp E p μ) : α → E)
  refine ⟨f, Lp.ext ?_⟩
  have hfc : (f : α → E) =ᵐ[μ] ((a⁻¹ • g : Lp E p μ) : α → E) :=
    (Measure.ae_smul_measure_iff hc).mp
      (MemLp.coeFn_toLp ((Lp.memLp (a⁻¹ • g)).smul_measure hc'))
  have hf : (f : α → E) =ᵐ[μ] a⁻¹ • (g : α → E) := hfc.trans (Lp.coeFn_smul a⁻¹ g)
  filter_upwards [lebesgueLpMeasureScaleValue_coe (𝕜 := 𝕜) c hc hc' f, hf] with x h₁ h₂
  change lebesgueLpMeasureScaleValue (𝕜 := 𝕜) (μ := μ) c hc hc' f x = g x
  rw [h₁, h₂]
  exact smul_inv_smul₀ ha (g x)

def lebesgueLpMeasureScaleEquiv (hp : p ≠ ∞)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ∞) :
    Lp E p (c • μ) ≃ₗᵢ[𝕜] Lp E p μ :=
  LinearIsometryEquiv.ofSurjective (lebesgueLpMeasureScale hp c hc hc')
    (lebesgueLpMeasureScale_surjective hp c hc hc')

end ThesisCommon

