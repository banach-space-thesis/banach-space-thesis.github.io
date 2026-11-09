import SurveyStatements.P5VectorPartitionTransfer

/-! Exact finite transport of Banach-valued indicators. These identities
stabilize the finite exterior maps on dyadic step functions. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5

variable {𝕜 α E ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [Fintype ι]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

local instance vectorPartIndicatorModuleReal : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
local instance vectorPartIndicatorScalarTower : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
local instance vectorPartIndicatorNormedSpaceReal : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

theorem vectorLpPartitionAverage_indicator (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hm : ∀ i, μ (s i) ≠ 0) (i j : ι) (c : E) :
    vectorLpPartitionAverage (𝕜 := 𝕜) hp (s j)
      (indicatorConstLp p (hs i) (measure_ne_top μ (s i)) c) =
        if j = i then c else 0 := by
  rw [← vectorLpExtend_const (𝕜 := 𝕜) (s i) (hs i) c]
  change (μ.real (s j) : 𝕜)⁻¹ •
      finiteLpIntegral (𝕜 := 𝕜) hp
        (P5Support.lebesgueLpRestrict (𝕜 := 𝕜) (s j)
          (P5Support.lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)
            (Lp.const p (μ.restrict (s i)) c))) = _
  by_cases hji : j = i
  · subst j
    rw [P5Support.lebesgueLpRestrict_extend, finiteLpIntegral_apply,
      integral_congr_ae (Lp.coeFn_const p (μ.restrict (s i)) c)]
    have hne : (μ.real (s i) : 𝕜) ≠ 0 := by
      exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hm i, measure_ne_top μ (s i)⟩)
    change ((μ (s i)).toReal : 𝕜) ≠ 0 at hne
    simp only [Function.const_apply, integral_const, measureReal_def,
      Measure.restrict_apply_univ, if_pos rfl]
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul, inv_mul_cancel₀ hne, one_smul]
    simp
  · rw [P5Support.lebesgueLpRestrict_extend_disjoint (hs j) (hs i) (hd hji), map_zero]
    simp only [smul_zero, if_neg hji]

theorem vectorLpPartitionTransfer_indicator (hp : p ≠ ∞) (s t : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ i, MeasurableSet (t i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hm : ∀ i, μ (s i) ≠ 0) (i : ι) (c : E) :
    vectorLpPartitionTransfer (𝕜 := 𝕜) hp s t ht
      (indicatorConstLp p (hs i) (measure_ne_top μ (s i)) c) =
        indicatorConstLp p (ht i) (measure_ne_top μ (t i)) c := by
  rw [vectorLpPartitionTransfer_apply]
  unfold vectorLpPartitionStep
  simp_rw [vectorLpPartitionAverage_indicator hp s hs hd hm]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg hji]
    rw [← vectorLpIndicator_apply (𝕜 := 𝕜)]
    exact map_zero _
  · simp

theorem vectorLpPartitionMean_fix_indicator (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hm : ∀ i, μ (s i) ≠ 0) (i : ι) (c : E) :
    vectorLpPartitionMean (𝕜 := 𝕜) hp s hs hd hc hm
      (indicatorConstLp p (hs i) (measure_ne_top μ (s i)) c) =
        indicatorConstLp p (hs i) (measure_ne_top μ (s i)) c := by
  rw [vectorLpPartitionMean_eq_step]
  have h := vectorLpPartitionTransfer_indicator (𝕜 := 𝕜) hp s s hs hs hd hm i c
  rw [vectorLpPartitionTransfer_apply] at h
  exact h

end SurveyStatements.P5
