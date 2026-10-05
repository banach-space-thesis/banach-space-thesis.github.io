import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import ThesisCommon.Analysis.L1IndicatorExt

/-! Actual trimmed L1 spaces as closed sublattices of the ambient L1 space. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
namespace ThesisCommon
variable {X : Type*} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)
variable {m : MeasurableSpace X}

abbrev lOneSubsigma (m : MeasurableSpace X) : Submodule ℝ (Lp ℝ 1 μ) :=
  @lpMeas X ℝ ℝ _ _ _ m m₀ 1 μ

def lOneSubsigmaEmbedding (hm : m ≤ m₀) :
    Lp ℝ 1 (μ.trim hm) →ₗᵢ[ℝ] Lp ℝ 1 μ :=
  (lOneSubsigma μ m).subtypeₗᵢ.comp
    (lpMeasToLpTrimLie ℝ ℝ 1 μ hm).symm.toLinearIsometry

theorem lOneSubsigmaEmbedding_ae_eq (hm : m ≤ m₀) (f : Lp ℝ 1 (μ.trim hm)) :
    lOneSubsigmaEmbedding μ hm f =ᵐ[μ] f := lpTrimToLpMeas_ae_eq (𝕜 := ℝ) hm f

theorem range_lOneSubsigmaEmbedding (hm : m ≤ m₀) :
    Set.range (lOneSubsigmaEmbedding μ hm) = (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ((lpMeasToLpTrimLie ℝ ℝ 1 μ hm).symm g).property
  · intro hf
    refine ⟨lpMeasToLpTrimLie ℝ ℝ 1 μ hm ⟨f, hf⟩, ?_⟩
    change ((lpMeasToLpTrimLie ℝ ℝ 1 μ hm).symm
      (lpMeasToLpTrimLie ℝ ℝ 1 μ hm ⟨f, hf⟩)).val = f
    rw [LinearIsometryEquiv.symm_apply_apply]

theorem isClosed_lOneSubsigma (hm : m ≤ m₀) :
    IsClosed (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) :=
  isClosed_aestronglyMeasurable hm

theorem lOneSubsigma_mono {m' : MeasurableSpace X} (h : m ≤ m') :
    lOneSubsigma μ m ≤ lOneSubsigma μ m' := by
  intro f hf
  exact AEStronglyMeasurable.mono h hf

theorem lOneSubsigma_sup_mem {f g : Lp ℝ 1 μ}
    (hf : f ∈ lOneSubsigma μ m) (hg : g ∈ lOneSubsigma μ m) :
    f ⊔ g ∈ lOneSubsigma μ m := by
  change AEStronglyMeasurable[m] f μ at hf
  change AEStronglyMeasurable[m] g μ at hg
  exact ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    (Lp.coeFn_sup f g).trans (hf.ae_eq_mk.sup hg.ae_eq_mk)⟩

theorem lOneSubsigma_inf_mem {f g : Lp ℝ 1 μ}
    (hf : f ∈ lOneSubsigma μ m) (hg : g ∈ lOneSubsigma μ m) :
    f ⊓ g ∈ lOneSubsigma μ m := by
  change AEStronglyMeasurable[m] f μ at hf
  change AEStronglyMeasurable[m] g μ at hg
  exact ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    (Lp.coeFn_inf f g).trans (hf.ae_eq_mk.inf hg.ae_eq_mk)⟩

theorem lOneSubsigma_abs_mem {f : Lp ℝ 1 μ} (hf : f ∈ lOneSubsigma μ m) :
    |f| ∈ lOneSubsigma μ m :=
  lOneSubsigma_sup_mem μ hf ((lOneSubsigma μ m).neg_mem hf)

theorem lOneSubsigmaEmbedding_sup (hm : m ≤ m₀) (f g : Lp ℝ 1 (μ.trim hm)) :
    lOneSubsigmaEmbedding μ hm (f ⊔ g) =
      lOneSubsigmaEmbedding μ hm f ⊔ lOneSubsigmaEmbedding μ hm g := by
  apply Lp.ext
  filter_upwards [lOneSubsigmaEmbedding_ae_eq μ hm (f ⊔ g),
    ae_eq_of_ae_eq_trim (Lp.coeFn_sup f g),
    Lp.coeFn_sup (lOneSubsigmaEmbedding μ hm f) (lOneSubsigmaEmbedding μ hm g),
    lOneSubsigmaEmbedding_ae_eq μ hm f, lOneSubsigmaEmbedding_ae_eq μ hm g]
    with x h₁ h₂ h₃ h₄ h₅
  simp only [h₁, h₂, h₃, Pi.sup_apply, h₄, h₅]

theorem lOneSubsigmaEmbedding_le_iff (hm : m ≤ m₀) (f g : Lp ℝ 1 (μ.trim hm)) :
    lOneSubsigmaEmbedding μ hm f ≤ lOneSubsigmaEmbedding μ hm g ↔ f ≤ g := by
  rw [← sup_eq_right, ← lOneSubsigmaEmbedding_sup,
    (lOneSubsigmaEmbedding μ hm).injective.eq_iff, sup_eq_right]

theorem lOneSubsigmaEmbedding_abs (hm : m ≤ m₀) (f : Lp ℝ 1 (μ.trim hm)) :
    lOneSubsigmaEmbedding μ hm |f| = |lOneSubsigmaEmbedding μ hm f| := by
  change lOneSubsigmaEmbedding μ hm (f ⊔ -f) =
    lOneSubsigmaEmbedding μ hm f ⊔ -lOneSubsigmaEmbedding μ hm f
  rw [lOneSubsigmaEmbedding_sup, map_neg]

theorem lOneSubsigmaEmbedding_const [IsFiniteMeasure μ] (hm : m ≤ m₀) (c : ℝ) :
    lOneSubsigmaEmbedding μ hm (Lp.const 1 (μ.trim hm) c) = Lp.const 1 μ c := by
  apply Lp.ext
  exact (lOneSubsigmaEmbedding_ae_eq μ hm _).trans
    ((ae_eq_of_ae_eq_trim (Lp.coeFn_const 1 (μ.trim hm) c)).trans (Lp.coeFn_const 1 μ c).symm)

theorem lOneSubsigmaEmbedding_indicator [IsFiniteMeasure μ] (hm : m ≤ m₀)
    (s : Set X) (hs : MeasurableSet[m] s) :
    lOneSubsigmaEmbedding μ hm (lOneIndicator (μ.trim hm) s hs) =
      lOneIndicator (mX := m₀) μ s (hm s hs) := by
  apply Lp.ext
  exact (lOneSubsigmaEmbedding_ae_eq μ hm _).trans
    ((ae_eq_of_ae_eq_trim (lOneIndicator_coe (μ := μ.trim hm) s hs)).trans
      (lOneIndicator_coe (mX := m₀) (μ := μ) s (hm s hs)).symm)

theorem integral_lOneSubsigmaEmbedding (hm : m ≤ m₀) (f : Lp ℝ 1 (μ.trim hm)) :
    ∫ x, lOneSubsigmaEmbedding μ hm f x ∂μ = ∫ x, f x ∂μ.trim hm :=
  (integral_congr_ae (lOneSubsigmaEmbedding_ae_eq μ hm f)).trans
    (integral_trim hm (Lp.stronglyMeasurable f))

theorem isSeparable_lOneSubsigma [IsFiniteMeasure μ] (hm : m ≤ m₀)
    [@MeasurableSpace.CountablyGenerated X m] :
    TopologicalSpace.IsSeparable (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) := by
  letI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  rw [← range_lOneSubsigmaEmbedding μ hm]
  exact isSeparable_range (lOneSubsigmaEmbedding μ hm).continuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lOneSubsigmaLift (hm : m ≤ m₀) (T : E →L[ℝ] Lp ℝ 1 μ)
    (hT : ∀ x, T x ∈ lOneSubsigma μ m) : E →L[ℝ] Lp ℝ 1 (μ.trim hm) :=
  (lpMeasToLpTrimLie ℝ ℝ 1 μ hm).toLinearIsometry.toContinuousLinearMap.comp
    (T.codRestrict (lOneSubsigma μ m) hT)

theorem lOneSubsigmaEmbedding_lift (hm : m ≤ m₀) (T : E →L[ℝ] Lp ℝ 1 μ)
    (hT : ∀ x, T x ∈ lOneSubsigma μ m) :
    (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap.comp
      (lOneSubsigmaLift μ hm T hT) = T := by
  apply ContinuousLinearMap.ext
  intro x
  change ((lpMeasToLpTrimLie ℝ ℝ 1 μ hm).symm
    (lpMeasToLpTrimLie ℝ ℝ 1 μ hm ⟨T x, hT x⟩)).val = T x
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem norm_lOneSubsigmaLift (hm : m ≤ m₀) (T : E →L[ℝ] Lp ℝ 1 μ)
    (hT : ∀ x, T x ∈ lOneSubsigma μ m) : ‖lOneSubsigmaLift μ hm T hT‖ = ‖T‖ := by
  have hnorm (x : E) : ‖lOneSubsigmaLift μ hm T hT x‖ = ‖T x‖ :=
    (lpMeasToLpTrimLie ℝ ℝ 1 μ hm).norm_map ⟨T x, hT x⟩
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [hnorm]
    exact T.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← hnorm]
    exact (lOneSubsigmaLift μ hm T hT).le_opNorm x

end ThesisCommon
