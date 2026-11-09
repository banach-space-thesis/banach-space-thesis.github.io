import BanachIsometric.SmoothApproximationSequence
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Boundary avoidance survives actual endpoint mollification

For the straight-line homotopy between two Lipschitz maps, a compact boundary
image disjoint from a closed target set stays disjoint after sufficiently fine
mollification of both endpoints. This is the stability step needed to apply
the smooth divergence calculation and pass to Lipschitz endpoints.
-/

namespace BanachIsometric

open Set Metric Filter MeasureTheory
open scoped Topology NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def realAffine (t : ℝ) (u v : F) : F := (1 - t) • u + t • v

theorem dist_realAffine_le_add (t : unitInterval) (u v u' v' : F) :
    dist (realAffine t u v) (realAffine t u' v') ≤ dist u u' + dist v v' := by
  rw [dist_eq_norm]
  have he : realAffine t u v - realAffine t u' v' =
      (1 - (t : ℝ)) • (u - u') + (t : ℝ) • (v - v') := by
    simp only [realAffine, smul_sub]
    abel
  rw [he]
  calc
    ‖(1 - (t : ℝ)) • (u - u') + (t : ℝ) • (v - v')‖ ≤
        ‖(1 - (t : ℝ)) • (u - u')‖ + ‖(t : ℝ) • (v - v')‖ := norm_add_le _ _
    _ = (1 - (t : ℝ)) * ‖u - u'‖ + (t : ℝ) * ‖v - v'‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr t.property.2),
        Real.norm_of_nonneg t.property.1]
    _ ≤ dist u u' + dist v v' := by
      rw [dist_eq_norm, dist_eq_norm]
      nlinarith [norm_nonneg (u - u'), norm_nonneg (v - v'), t.property.1, t.property.2]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F]

theorem eventually_mollified_affine_boundary_avoids_closed
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f₀ f₁ : E → F} {C₀ C₁ : ℝ≥0} (hf₀ : LipschitzWith C₀ f₀) (hf₁ : LipschitzWith C₁ f₁)
    {b : Set E} (hb : IsCompact b) {T : Set F} (hT : IsClosed T)
    (havoid : ∀ x ∈ b, ∀ t : unitInterval, realAffine t (f₀ x) (f₁ x) ∉ T) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ b, ∀ t : unitInterval,
      realAffine t (smoothBumpConvolution μ (shrinkingBump E n) f₀ x)
        (smoothBumpConvolution μ (shrinkingBump E n) f₁ x) ∉ T := by
  letI : CompactSpace b := isCompact_iff_compactSpace.mp hb
  let H : unitInterval × b → F := fun z => realAffine z.1 (f₀ z.2) (f₁ z.2)
  have hH : Continuous H := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hf₀.continuous.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (hf₁.continuous.comp (continuous_subtype_val.comp continuous_snd)))
  have hK : IsCompact (Set.range H) := isCompact_range hH
  have hsub : Set.range H ⊆ Tᶜ := by
    rintro _ ⟨⟨t, x⟩, rfl⟩
    exact havoid x x.property t
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hT.isOpen_compl hsub
  have ht : Tendsto (fun n => ((C₀ : ℝ) + (C₁ : ℝ)) * (shrinkingBump E n).rOut)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (shrinkingBump_rOut_tendsto (E := E)).const_mul ((C₀ : ℝ) + (C₁ : ℝ))
  filter_upwards [(tendsto_order.mp ht).2 δ hδ] with n hn
  intro x hx t
  apply hthick
  apply mem_thickening_iff.mpr
  refine ⟨H (t, ⟨x, hx⟩), mem_range_self _, ?_⟩
  calc
    dist (realAffine t (smoothBumpConvolution μ (shrinkingBump E n) f₀ x)
        (smoothBumpConvolution μ (shrinkingBump E n) f₁ x)) (H (t, ⟨x, hx⟩)) ≤
        dist (smoothBumpConvolution μ (shrinkingBump E n) f₀ x) (f₀ x) +
          dist (smoothBumpConvolution μ (shrinkingBump E n) f₁ x) (f₁ x) :=
      dist_realAffine_le_add t _ _ _ _
    _ ≤ (C₀ : ℝ) * (shrinkingBump E n).rOut +
        (C₁ : ℝ) * (shrinkingBump E n).rOut :=
      add_le_add (dist_smoothBumpConvolution_le μ _ hf₀ x)
        (dist_smoothBumpConvolution_le μ _ hf₁ x)
    _ < δ := by rwa [← add_mul]

end BanachIsometric
