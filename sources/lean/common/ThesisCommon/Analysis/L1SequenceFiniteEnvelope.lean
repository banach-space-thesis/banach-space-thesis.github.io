import ThesisCommon.Analysis.SupportedWeakEssentialNormAssembly
import ThesisCommon.Analysis.L1DensityEquivRCLike
import ThesisCommon.Analysis.L1OperatorRangeFactor
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-! Any countable family in actual real or complex L1 is contained in the
isometric image of an L1 space with finite measure. This needs no assumption
on the original measure and no separable sigma-algebra projection. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem exists_sigmaFinite_lOne_sequence_support (f : ℕ → Lp 𝕜 1 μ) :
    ∃ Ω : Set X, MeasurableSet Ω ∧ SigmaFinite (μ.restrict Ω) ∧
      ∀ n, f n =ᵐ[μ.restrict Ωᶜ] 0 := by
  choose Ω hΩ hz hσ using fun n =>
    (L1.integrable_coeFn (f n)).aefinStronglyMeasurable.exists_set_sigmaFinite
  refine ⟨⋃ n, Ω n, MeasurableSet.iUnion hΩ,
    sigmaFinite_restrict_countable_iUnion Ω hΩ hσ, fun n => ?_⟩
  exact (hz n).filter_mono (ae_mono
    (Measure.restrict_mono (compl_subset_compl.mpr (subset_iUnion Ω n)) le_rfl))

theorem exists_finite_lOne_isometric_sequence_envelope (f : ℕ → Lp 𝕜 1 μ) :
    ∃ ρ : Measure X, IsFiniteMeasure ρ ∧
      ∃ J : Lp 𝕜 1 ρ →ₗᵢ[𝕜] Lp 𝕜 1 μ,
        ∃ v : ℕ → Lp 𝕜 1 ρ, ∀ n, J (v n) = f n := by
  obtain ⟨Ω, hΩ, hσ, hs⟩ := exists_sigmaFinite_lOne_sequence_support f
  letI := hσ
  obtain ⟨g, hg, hpos, hfin⟩ := exists_positive_finite_density (μ.restrict Ω)
  let ρ := (μ.restrict Ω).withDensity (fun x => (g x : ENNReal))
  let e := lOneWithDensityEquiv_rclike (𝕜 := 𝕜) hg hpos
  let J := (lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ).comp e.toLinearIsometry
  refine ⟨ρ, hfin, J, fun n => e.symm (lebesgueLpRestrict (𝕜 := 𝕜) Ω (f n)), fun n => ?_⟩
  change lebesgueLpExtend (𝕜 := 𝕜) Ω hΩ
    (e (e.symm (lebesgueLpRestrict (𝕜 := 𝕜) Ω (f n)))) = f n
  rw [e.apply_symm_apply]
  exact lebesgueLpExtend_restrict_of_supported Ω hΩ (f n) (hs n)

end ThesisCommon
