import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Restriction and zero extension on the actual measure-theoretic `Lp` spaces.
These are the block operators used for the measurable interval decomposition. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace ThesisCommon
variable {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

def lebesgueLpRestrict (s : Set α) : Lp E p μ →L[𝕜] Lp E p (μ.restrict s) :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).restrict s).toLp f
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict s),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict s),
          MemLp.coeFn_toLp ((Lp.memLp g).restrict s),
          ae_restrict_of_ae (Lp.coeFn_add f g),
          Lp.coeFn_add (((Lp.memLp f).restrict s).toLp f)
            (((Lp.memLp g).restrict s).toLp g)] with x h₁ h₂ h₃ h₄ h₅
        simp only [Pi.add_apply] at h₄ h₅
        rw [h₁, h₄, h₅, h₂, h₃]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict s),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict s),
          ae_restrict_of_ae (Lp.coeFn_smul c f),
          Lp.coeFn_smul c (((Lp.memLp f).restrict s).toLp f)] with x h₁ h₂ h₃ h₄
        simp only [Pi.smul_apply] at h₃ h₄
        simpa only [h₁, h₃, h₄, h₂, RingHom.id_apply] }
    1 (fun f => by
      change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ 1 * ‖f‖
      rw [Lp.norm_toLp, one_mul]
      exact
        ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le f p μ s))

theorem lebesgueLpRestrict_coe (s : Set α) (f : Lp E p μ) :
    lebesgueLpRestrict (𝕜 := 𝕜) s f =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

theorem norm_lebesgueLpRestrict_le (s : Set α) :
    ‖lebesgueLpRestrict (𝕜 := 𝕜) (E := E) (p := p) (μ := μ) s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def lebesgueLpExtendValue (s : Set α) (hs : MeasurableSet s)
    (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator f)

set_option maxHeartbeats 800000 in
theorem lebesgueLpExtendValue_coe (s : Set α) (hs : MeasurableSet s)
    (f : Lp E p (μ.restrict s)) :
    lebesgueLpExtendValue (μ := μ) s hs f =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp
    ((memLp_indicator_iff_restrict (μ := μ) (p := p) (f := (f : α → E)) hs).mpr
      (Lp.memLp f))

def lebesgueLpExtend (s : Set α) (hs : MeasurableSet s) :
    Lp E p (μ.restrict s) →ₗᵢ[𝕜] Lp E p μ where
  toFun := lebesgueLpExtendValue (μ := μ) s hs
  map_add' f g := by
    apply Lp.ext
    have hadd := (ae_restrict_iff' hs).mp (Lp.coeFn_add f g)
    filter_upwards [lebesgueLpExtendValue_coe (μ := μ) s hs (f + g),
      lebesgueLpExtendValue_coe (μ := μ) s hs f,
      lebesgueLpExtendValue_coe (μ := μ) s hs g,
      Lp.coeFn_add (lebesgueLpExtendValue (μ := μ) s hs f) (lebesgueLpExtendValue (μ := μ) s hs g),
      hadd] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₄, Pi.add_apply, h₂, h₃]
    by_cases hx : x ∈ s
    · simpa [hx] using h₅ hx
    · simp [hx]
  map_smul' c f := by
    apply Lp.ext
    have hsmul := (ae_restrict_iff' hs).mp (Lp.coeFn_smul c f)
    filter_upwards [lebesgueLpExtendValue_coe (μ := μ) s hs (c • f),
      lebesgueLpExtendValue_coe (μ := μ) s hs f,
      Lp.coeFn_smul c (lebesgueLpExtendValue (μ := μ) s hs f),
      hsmul] with x h₁ h₂ h₃ h₄
    simp only [RingHom.id_apply]
    rw [h₁, h₃, Pi.smul_apply, h₂]
    by_cases hx : x ∈ s
    · simpa [hx] using h₄ hx
    · simp [hx]
  norm_map' f := by
    change ‖lebesgueLpExtendValue (μ := μ) s hs f‖ = ‖f‖
    unfold lebesgueLpExtendValue
    rw [Lp.norm_toLp,
      eLpNorm_indicator_eq_eLpNorm_restrict hs, Lp.norm_def]

theorem lebesgueLpExtend_coe (s : Set α) (hs : MeasurableSet s)
    (f : Lp E p (μ.restrict s)) :
    lebesgueLpExtend (𝕜 := 𝕜) s hs f =ᵐ[μ] s.indicator f :=
  lebesgueLpExtendValue_coe (μ := μ) s hs f

theorem lebesgueLpRestrict_extend (s : Set α) (hs : MeasurableSet s)
    (f : Lp E p (μ.restrict s)) :
    lebesgueLpRestrict (𝕜 := 𝕜) s (lebesgueLpExtend (𝕜 := 𝕜) s hs f) = f := by
  apply Lp.ext
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) s (lebesgueLpExtend (𝕜 := 𝕜) s hs f),
    ae_restrict_of_ae (lebesgueLpExtend_coe (𝕜 := 𝕜) s hs f), ae_restrict_mem hs]
    with x h₁ h₂ hx
  simp [h₁, h₂, hx]

theorem lebesgueLpRestrict_extend_disjoint {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) (f : Lp E p (μ.restrict t)) :
    lebesgueLpRestrict (𝕜 := 𝕜) s (lebesgueLpExtend (𝕜 := 𝕜) t ht f) = 0 := by
  apply Lp.ext
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) s (lebesgueLpExtend (𝕜 := 𝕜) t ht f),
    ae_restrict_of_ae (lebesgueLpExtend_coe (𝕜 := 𝕜) t ht f), ae_restrict_mem hs,
    Lp.coeFn_zero E p (μ.restrict s)] with x h₁ h₂ hx h₀
  rw [h₁, h₂, h₀]
  exact Set.indicator_of_notMem (fun hxt => Set.disjoint_left.mp hst hx hxt) _

end ThesisCommon


