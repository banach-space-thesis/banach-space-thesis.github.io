import ThesisCommon.Analysis.RCLikeL1DensityCuts
import ThesisCommon.Analysis.ComplexL1SigmaFiniteRange

/-! A sigma-finite output support has an actual finite-measure L1 model,
with contractive retraction, isometric zero-extension/density embedding,
and exact preservation of all measurable output cuts. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {𝕜 E Y : Type*} [RCLike 𝕜] [MeasurableSpace Y]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] {ν : Measure Y}

structure FiniteL1RangeFactor (T : E →L[𝕜] Lp 𝕜 1 ν) where
  measure : Measure Y
  finite : IsFiniteMeasure measure
  embed : Lp 𝕜 1 measure →ₗᵢ[𝕜] Lp 𝕜 1 ν
  retract : Lp 𝕜 1 ν →L[𝕜] Lp 𝕜 1 measure
  norm_retract_le : ‖retract‖ ≤ 1
  left_inv : ∀ f, retract (embed f) = f
  factor : embed.toContinuousLinearMap.comp (retract.comp T) = T
  commute_cut : ∀ A, ∀ hA : MeasurableSet A, ∀ f,
    embed (lpCut A hA f) = lpCut A hA (embed f)

theorem exists_finiteL1RangeFactor_of_supported
    (T : E →L[𝕜] Lp 𝕜 1 ν) (Ω : Set Y) (hΩ : MeasurableSet Ω)
    [SigmaFinite (ν.restrict Ω)] (hs : ∀ f, T f =ᵐ[ν.restrict Ωᶜ] 0) :
    Nonempty (FiniteL1RangeFactor T) := by
  obtain ⟨g, hg, hpos, hfin⟩ := exists_positive_finite_density (ν.restrict Ω)
  let e := lOneWithDensityEquiv_rclike (𝕜 := 𝕜) hg hpos
  let J := (lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ).comp e.toLinearIsometry
  let Q := e.symm.toLinearIsometry.toContinuousLinearMap.comp (lebesgueLpRestrict (𝕜 := 𝕜) Ω)
  refine ⟨⟨_, hfin, J, Q, ?_, ?_, ?_, ?_⟩⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul e.symm.toLinearIsometry.norm_toContinuousLinearMap_le
        (norm_lebesgueLpRestrict_le (𝕜 := 𝕜) (E := 𝕜) (p := 1) (μ := ν) Ω)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  · intro f
    change e.symm (lebesgueLpRestrict (𝕜 := 𝕜) Ω (lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ (e f))) = f
    rw [lebesgueLpRestrict_extend, e.symm_apply_apply]
  · apply ContinuousLinearMap.ext
    intro f
    change lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ
      (e (e.symm (lebesgueLpRestrict (𝕜 := 𝕜) Ω (T f)))) = T f
    rw [e.apply_symm_apply]
    exact lebesgueLpExtend_restrict_of_supported Ω hΩ (T f) (hs f)
  · intro A hA f
    change lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ (e (lpCut A hA f)) =
      lpCut A hA (lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ (e f))
    rw [lOneWithDensityEquiv_rclike_cut hg hpos, lebesgueL1Extend_cut_rclike]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exists_finiteL1RangeFactor_real [IsFiniteMeasure μ]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : Nonempty (FiniteL1RangeFactor T) := by
  obtain ⟨Ω, hΩ, hσ, hs⟩ := exists_sigmaFinite_range_part T
  letI := hσ
  exact exists_finiteL1RangeFactor_of_supported T Ω hΩ hs

theorem exists_finiteL1RangeFactor_complex [SigmaFinite μ]
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) : Nonempty (FiniteL1RangeFactor T) := by
  obtain ⟨Ω, hΩ, hσ, hs⟩ := exists_sigmaFinite_range_part_complex_sigmaFinite T
  letI := hσ
  exact exists_finiteL1RangeFactor_of_supported T Ω hΩ hs

end ThesisCommon
