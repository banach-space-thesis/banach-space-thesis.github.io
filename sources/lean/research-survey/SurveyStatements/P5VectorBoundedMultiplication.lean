import SurveyStatements.P5Averages

/-! Actual contractive pointwise multiplication on vector-valued Lp.
This includes restriction to measurable outer or inner cells. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical

namespace SurveyStatements.P5
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem vectorBoundedMultiply_memLp (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp E p unitIntervalMeasure) :
    MemLp (fun x => η x • f x) p unitIntervalMeasure := by
  apply (Lp.memLp f).of_le (hη.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
  apply Eventually.of_forall
  intro x
  change ‖η x • f x‖ ≤ ‖f x‖
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x))).trans_eq (one_mul _)

def vectorBoundedMultiplyValue (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp E p unitIntervalMeasure) :
    Lp E p unitIntervalMeasure :=
  (vectorBoundedMultiply_memLp η hη hb f).toLp (fun x => η x • f x)

theorem vectorBoundedMultiplyValue_ae (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp E p unitIntervalMeasure) :
    vectorBoundedMultiplyValue η hη hb f =ᵐ[unitIntervalMeasure] fun x => η x • f x :=
  MemLp.coeFn_toLp _

theorem norm_vectorBoundedMultiplyValue_le (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (f : Lp E p unitIntervalMeasure) :
    ‖vectorBoundedMultiplyValue η hη hb f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [vectorBoundedMultiplyValue_ae η hη hb f] with x hx
  rw [hx, norm_smul]
  exact (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x))).trans_eq (one_mul _)

def vectorBoundedMultiply (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  LinearMap.mkContinuous
    { toFun := vectorBoundedMultiplyValue η hη hb
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [vectorBoundedMultiplyValue_ae η hη hb (f + g),
          vectorBoundedMultiplyValue_ae η hη hb f, vectorBoundedMultiplyValue_ae η hη hb g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (vectorBoundedMultiplyValue η hη hb f)
            (vectorBoundedMultiplyValue η hη hb g)] with x h₁ h₂ h₃ h₄ h₅
        simp only [Pi.add_apply] at h₄ h₅
        rw [h₁, h₄, h₅, h₂, h₃, smul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [vectorBoundedMultiplyValue_ae η hη hb (c • f),
          vectorBoundedMultiplyValue_ae η hη hb f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (vectorBoundedMultiplyValue η hη hb f)] with x h₁ h₂ h₃ h₄
        simp only [Pi.smul_apply] at h₃ h₄
        simp only [RingHom.id_apply]
        rw [h₁, h₃, h₄, h₂]
        exact smul_comm _ _ _ }
    1 (fun f => by simpa only [one_mul] using norm_vectorBoundedMultiplyValue_le η hη hb f)

theorem norm_vectorBoundedMultiply_le (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : ‖vectorBoundedMultiply (E := E) (p := p) η hη hb‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def vectorIndicatorMultiply (s : Set ℝ) (hs : MeasurableSet s) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  vectorBoundedMultiply (s.indicator (fun _ => (1 : 𝕜)))
    (stronglyMeasurable_const.indicator hs) (fun x => by
      by_cases hx : x ∈ s <;> simp [hx])

theorem norm_vectorIndicatorMultiply_le (s : Set ℝ) (hs : MeasurableSet s) :
    ‖vectorIndicatorMultiply (𝕜 := 𝕜) (E := E) (p := p) s hs‖ ≤ 1 :=
  norm_vectorBoundedMultiply_le _ _ _

theorem vectorIndicatorMultiply_ae (s : Set ℝ) (hs : MeasurableSet s)
    (f : Lp E p unitIntervalMeasure) :
    vectorIndicatorMultiply (𝕜 := 𝕜) s hs f =ᵐ[unitIntervalMeasure] s.indicator f := by
  filter_upwards [vectorBoundedMultiplyValue_ae (s.indicator (fun _ => (1 : 𝕜)))
    (stronglyMeasurable_const.indicator hs) (fun x => by
      by_cases hx : x ∈ s <;> simp [hx]) f] with x hx
  change (vectorIndicatorMultiply (𝕜 := 𝕜) s hs f) x = _ at hx
  rw [hx]
  by_cases hmem : x ∈ s <;> simp [hmem]

theorem vectorIndicatorMultiply_idempotent (s : Set ℝ) (hs : MeasurableSet s) :
    (vectorIndicatorMultiply (𝕜 := 𝕜) (E := E) (p := p) s hs).comp
      (vectorIndicatorMultiply (𝕜 := 𝕜) s hs) = vectorIndicatorMultiply (𝕜 := 𝕜) s hs := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [vectorIndicatorMultiply_ae (𝕜 := 𝕜) s hs
    (vectorIndicatorMultiply (𝕜 := 𝕜) s hs f),
    vectorIndicatorMultiply_ae (𝕜 := 𝕜) s hs f] with x h₁ h₂
  change (vectorIndicatorMultiply (𝕜 := 𝕜) s hs
    (vectorIndicatorMultiply (𝕜 := 𝕜) s hs f)) x =
      (vectorIndicatorMultiply (𝕜 := 𝕜) s hs f) x
  rw [h₁, h₂]
  by_cases hx : x ∈ s <;> simp [hx, h₂]

end SurveyStatements.P5
