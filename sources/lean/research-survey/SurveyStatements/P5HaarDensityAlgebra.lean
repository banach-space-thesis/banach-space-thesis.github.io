import SurveyStatements.P5HaarDensityChildren
import SurveyStatements.P5HaarDensityStep
import Mathlib.Tactic.Abel

/-! Finite Haar expansions of dyadic scalar indicators. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem haarDensityIndicator_children_add (I : DyadicIndex) (c : E) :
    haarDensityIndicator (p := p) I c =
      haarDensityIndicator (haarDensityLeftChild I) c +
        haarDensityIndicator (haarDensityRightChild I) c := by
  simp only [haarDensityIndicator, haarDensityLeftChild_cell, haarDensityRightChild_cell]
  simpa only [haarDensityCell_union] using
    (indicatorConstLp_disjoint_union (p := p) (μ := unitIntervalMeasure)
      (show MeasurableSet (dyadicLeft I) from measurableSet_Ico)
      (show MeasurableSet (dyadicRight I) from measurableSet_Ico)
      (measure_ne_top _ _) (measure_ne_top _ _) (haarDensityChildren_disjoint I) c)

theorem haarDensityHaar_children_sub (I : DyadicIndex) :
    dyadicHaar 𝕜 p I =
      haarDensityIndicator (haarDensityLeftChild I) (1 : 𝕜) -
        haarDensityIndicator (haarDensityRightChild I) (1 : 𝕜) := by
  simp only [haarDensityIndicator, haarDensityLeftChild_cell, haarDensityRightChild_cell,
    dyadicHaar]

theorem haarDensityIndicator_smul (I : DyadicIndex) (a : 𝕜) (c : E) :
    haarDensityIndicator (p := p) I (a • c) = a • haarDensityIndicator I c := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := p)
      (hs := (show MeasurableSet (haarDensityCell I) from measurableSet_Ico))
      (hμs := measure_ne_top unitIntervalMeasure _) (c := a • c),
    indicatorConstLp_coeFn (p := p)
      (hs := (show MeasurableSet (haarDensityCell I) from measurableSet_Ico))
      (hμs := measure_ne_top unitIntervalMeasure _) (c := c),
    Lp.coeFn_smul a (haarDensityIndicator (p := p) I c)] with x hleft hright hsmul
  change haarDensityIndicator (p := p) I (a • c) x = (a • haarDensityIndicator I c) x
  rw [hsmul]
  simp only [Pi.smul_apply]
  unfold haarDensityIndicator
  rw [hleft, hright]
  exact Set.indicator_smul_apply _ _ _ _

theorem haarDensityIndicator_root (i : Fin (2 ^ 0)) (c : E) :
    haarDensityIndicator (p := p) ⟨0, i⟩ c = Lp.const p unitIntervalMeasure c := by
  have hi : i.val = 0 := by have := i.isLt; norm_num at this; omega
  have hcell : haarDensityCell ⟨0, i⟩ = Ico (0 : ℝ) 1 := by
    simp [haarDensityCell, dyadicStart, dyadicEnd, hi]
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := p)
      (hs := (show MeasurableSet (haarDensityCell ⟨0, i⟩) from measurableSet_Ico))
      (hμs := measure_ne_top unitIntervalMeasure _) (c := c),
    Lp.coeFn_const p unitIntervalMeasure c, ae_mem_unitInterval_Ico] with x hleft hright hx
  change haarDensityIndicator (p := p) ⟨0, i⟩ c x = (Lp.const p unitIntervalMeasure c) x
  unfold haarDensityIndicator
  rw [hleft, hright, hcell, Set.indicator_of_mem hx]
  rfl

def haarDensityAugmentedSpan : Submodule 𝕜 (Lp 𝕜 p unitIntervalMeasure) :=
  Submodule.span 𝕜 (insert (Lp.const p unitIntervalMeasure (1 : 𝕜))
    (Set.range (dyadicHaar 𝕜 p)))

theorem haarDensityIndicator_one_mem_augmented (I : DyadicIndex) :
    haarDensityIndicator (p := p) I (1 : 𝕜) ∈ haarDensityAugmentedSpan (𝕜 := 𝕜) := by
  rcases I with ⟨n, i⟩
  induction n with
  | zero =>
    rw [haarDensityIndicator_root]
    exact Submodule.subset_span (Set.mem_insert _ _)
  | succ n ih =>
    obtain ⟨j, hleft | hright⟩ := haarDensityCell_is_child n i
    · rw [hleft]
      have hhaar : dyadicHaar 𝕜 p ⟨n, j⟩ ∈ haarDensityAugmentedSpan (𝕜 := 𝕜) :=
        Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨n, j⟩, rfl⟩)
      have hsum := (haarDensityAugmentedSpan (𝕜 := 𝕜) (p := p)).add_mem (ih j) hhaar
      have htwice : (2 : 𝕜) • haarDensityIndicator (p := p)
          (haarDensityLeftChild ⟨n, j⟩) (1 : 𝕜) =
          haarDensityIndicator ⟨n, j⟩ (1 : 𝕜) + dyadicHaar 𝕜 p ⟨n, j⟩ := by
        rw [haarDensityIndicator_children_add (p := p) ⟨n, j⟩ (1 : 𝕜),
          haarDensityHaar_children_sub (p := p) ⟨n, j⟩, two_smul]
        abel
      rw [← htwice] at hsum
      have h := (haarDensityAugmentedSpan (𝕜 := 𝕜) (p := p)).smul_mem (2 : 𝕜)⁻¹ hsum
      simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : 𝕜) ≠ 0), one_smul] using h
    · rw [hright]
      have hhaar : dyadicHaar 𝕜 p ⟨n, j⟩ ∈ haarDensityAugmentedSpan (𝕜 := 𝕜) :=
        Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨n, j⟩, rfl⟩)
      have hsum := (haarDensityAugmentedSpan (𝕜 := 𝕜) (p := p)).sub_mem (ih j) hhaar
      have htwice : (2 : 𝕜) • haarDensityIndicator (p := p)
          (haarDensityRightChild ⟨n, j⟩) (1 : 𝕜) =
          haarDensityIndicator ⟨n, j⟩ (1 : 𝕜) - dyadicHaar 𝕜 p ⟨n, j⟩ := by
        rw [haarDensityIndicator_children_add (p := p) ⟨n, j⟩ (1 : 𝕜),
          haarDensityHaar_children_sub (p := p) ⟨n, j⟩, two_smul]
        abel
      rw [← htwice] at hsum
      have h := (haarDensityAugmentedSpan (𝕜 := 𝕜) (p := p)).smul_mem (2 : 𝕜)⁻¹ hsum
      simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : 𝕜) ≠ 0), one_smul] using h

theorem haarDensityIndicator_mem_augmented (I : DyadicIndex) (c : 𝕜) :
    haarDensityIndicator (p := p) I c ∈ haarDensityAugmentedSpan (𝕜 := 𝕜) := by
  have heq : haarDensityIndicator (p := p) I c = c • haarDensityIndicator I (1 : 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using haarDensityIndicator_smul (p := p) I c (1 : 𝕜)
  rw [heq]
  exact (haarDensityAugmentedSpan (𝕜 := 𝕜) (p := p)).smul_mem c
    (haarDensityIndicator_one_mem_augmented I)

theorem haarDensityAugmentedSpan_closure (hp : p ≠ ∞) :
    (haarDensityAugmentedSpan (𝕜 := 𝕜) (p := p)).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← haarDensityStepSpace_closure_eq_top (𝕜 := 𝕜) (E := 𝕜) hp]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨I, c⟩, rfl⟩
  exact haarDensityIndicator_mem_augmented I c

end SurveyStatements.P5
