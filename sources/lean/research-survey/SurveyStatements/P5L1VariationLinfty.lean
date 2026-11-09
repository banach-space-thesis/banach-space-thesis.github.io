import SurveyStatements.P5L1VariationTrace

/-! The actual L∞ density representing every local trace of a bounded
scalar L¹ Haar multiplier. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

abbrev IntervalLinfty (𝕜 : Type*) [RCLike 𝕜] := IntervalLp 𝕜 ⟨∞, le_top⟩

theorem exists_full_trace_Linfty_density (𝕜 : Type*) [RCLike 𝕜]
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) :
    ∃ m : IntervalLinfty 𝕜, ‖m‖ ≤ ‖D‖ ∧
      ∀ s : Set ℝ, Tendsto (fun n => lpHaarLevelTrace d n s) atTop
        (𝓝 (∫ x in s, m x ∂(volume.restrict (Icc (0 : ℝ) 1)))) := by
  obtain ⟨m, hm, hbound, _, htrace⟩ := exists_full_trace_density 𝕜 D d hD
  have hmem : MemLp m ∞ (volume.restrict (Icc (0 : ℝ) 1)) :=
    memLp_top_of_bound hm.aestronglyMeasurable ‖D‖ hbound
  let M : IntervalLinfty 𝕜 := hmem.toLp m
  have hnorm : ‖M‖ ≤ ‖D‖ := by
    calc
      ‖M‖ = (eLpNorm m ∞ (volume.restrict (Icc (0 : ℝ) 1))).toReal := Lp.norm_toLp m hmem
      _ ≤ (ENNReal.ofReal ‖D‖).toReal :=
        ENNReal.toReal_mono (by simp) (eLpNormEssSup_le_of_ae_bound hbound)
      _ = ‖D‖ := ENNReal.toReal_ofReal (norm_nonneg D)
  refine ⟨M, hnorm, ?_⟩
  intro s
  have he : (∫ x in s, M x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
      ∫ x in s, m x ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
    integral_congr_ae (ae_restrict_of_ae hmem.coeFn_toLp)
  rw [he]
  exact htrace s

end SurveyStatements.P5L1Variation
