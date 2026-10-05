import ThesisCommon.Analysis.ContinuousMapJordan
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.CompactOpen

/-! Positive parts of weak-star kernels: clipped test functions yield genuine
lower semicontinuity without assuming weak-star continuity of the Jordan parts. -/
noncomputable section
namespace ThesisCommon
variable {K A : Type*} [TopologicalSpace K] [CompactSpace K] [TopologicalSpace A]

theorem continuousMap_positive_image_eq_range_clipped
    (μ : C(K, ℝ) →L[ℝ] ℝ) (f : C(K, ℝ)) (hf : 0 ≤ f) :
    μ '' Set.Icc 0 f = Set.range (fun g : C(K, ℝ) => μ (g⁺ ⊓ f)) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, ?_⟩
    dsimp only
    rw [show g⁺ = g from sup_eq_left.mpr hg.1, inf_eq_left.mpr hg.2]
  · rintro ⟨g, rfl⟩
    exact ⟨g⁺ ⊓ f, ⟨le_inf (posPart_nonneg g) hf, inf_le_right⟩, rfl⟩

theorem continuousMapPositiveValue_eq_ciSup_clipped
    (μ : C(K, ℝ) →L[ℝ] ℝ) (f : C(K, ℝ)) (hf : 0 ≤ f) :
    continuousMapPositiveValue μ f = ⨆ g : C(K, ℝ), μ (g⁺ ⊓ f) := by
  change sSup (μ '' Set.Icc 0 f) = sSup (Set.range _)
  rw [continuousMap_positive_image_eq_range_clipped μ f hf]

theorem lowerSemicontinuous_continuousMapPositivePart_test
    (μ : A → C(K, ℝ) →L[ℝ] ℝ) (f : A → C(K, ℝ)) (hf : ∀ a, 0 ≤ f a)
    (hμ : ∀ g : C(K, ℝ), Continuous (fun a => μ a (g⁺ ⊓ f a))) :
    LowerSemicontinuous (fun a => continuousMapPositivePart (μ a) (f a)) := by
  have heq : (fun a => continuousMapPositivePart (μ a) (f a)) =
      (fun a => ⨆ g : C(K, ℝ), μ a (g⁺ ⊓ f a)) := by
    funext a
    rw [continuousMapPositivePart_apply_nonneg _ (hf a),
      continuousMapPositiveValue_eq_ciSup_clipped _ _ (hf a)]
  rw [heq]
  apply lowerSemicontinuous_ciSup
  · intro a
    rw [← continuousMap_positive_image_eq_range_clipped _ _ (hf a)]
    exact continuousMap_positive_image_bddAbove _ _
  · exact fun g => (hμ g).lowerSemicontinuous

theorem continuous_continuousMap_clip [LocallyCompactSpace K]
    (f : A → C(K, ℝ)) (hf : Continuous f) (g : C(K, ℝ)) :
    Continuous (fun a => g⁺ ⊓ f a) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun ax : A × K => min (g⁺ ax.2) (f ax.1 ax.2))
  exact ((g⁺).continuous.comp continuous_snd).min
    (continuous_eval.comp ((hf.comp continuous_fst).prodMk continuous_snd))

end ThesisCommon
