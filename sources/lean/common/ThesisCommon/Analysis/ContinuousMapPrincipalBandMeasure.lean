import ThesisCommon.Analysis.ContinuousMapL1Density
import ThesisCommon.Analysis.ALRefinementPrincipal
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Positive elements of an actual principal band in C(K)* are exactly the
functionals whose finite Riesz measures are absolutely continuous with respect
to the generator's measure. The converse uses the actual singular part of
Lebesgue decomposition. The topological hypothesis holds for the interval. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]

theorem positiveContinuousMapRiesz_integral (μ : Measure K) [IsFiniteMeasure μ] :
    positiveContinuousMapRiesz (continuousMapIntegralCLM μ)
      (continuousMapIntegralCLM_nonneg μ) = μ := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact integral_positiveContinuousMapRiesz _ _ f.toContinuousMap

theorem positiveContinuousMap_mem_principalBand_iff
    (φ e : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) (he : 0 ≤ e) :
    φ ∈ principalBand e ↔
      positiveContinuousMapRiesz φ hφ ≪ positiveContinuousMapRiesz e he := by
  let ν := positiveContinuousMapRiesz φ hφ
  let μ := positiveContinuousMapRiesz e he
  have haφ : |φ| = φ := abs_of_nonneg hφ
  have hae : |e| = e := abs_of_nonneg he
  constructor
  · intro hband
    let S := ν.singularPart μ
    let θ := continuousMapIntegralCLM S
    have hθ : 0 ≤ θ := continuousMapIntegralCLM_nonneg S
    have haθ : |θ| = θ := abs_of_nonneg hθ
    have hθe : θ ⊓ e = 0 := by
      apply (positiveContinuousMapRiesz_mutuallySingular_iff θ e hθ he).mp
      rw [show positiveContinuousMapRiesz θ hθ = S from
        positiveContinuousMapRiesz_integral S]
      exact Measure.mutuallySingular_singularPart ν μ
    have hθφ : θ ≤ φ := by
      calc
        θ ≤ continuousMapIntegralCLM ν :=
          continuousMapIntegralCLM_mono (Measure.singularPart_le ν μ)
        _ = φ := continuousMapIntegralCLM_positiveContinuousMapRiesz φ hφ
    have hθmem : θ ∈ latticeDisjointComplement ({e} : Set (C(K, ℝ) →L[ℝ] ℝ)) := by
      intro z hz
      obtain rfl : z = e := hz
      simpa only [haθ, hae] using hθe
    have hφθ : |φ| ⊓ |θ| = 0 := hband θ hθmem
    have hzero : θ = 0 := by
      have hi : φ ⊓ θ = θ := inf_eq_right.mpr hθφ
      simpa only [haφ, haθ, hi] using hφθ
    have hS : S = 0 := (continuousMapIntegralCLM_eq_zero_iff S).mp hzero
    exact (Measure.singularPart_eq_zero ν μ).mp hS
  · intro hAC ψ hψ
    have hψe : |ψ| ⊓ e = 0 := by
      simpa only [hae] using hψ e (mem_singleton e)
    have hsing : positiveContinuousMapRiesz e he ⟂ₘ
        positiveContinuousMapRiesz |ψ| (abs_nonneg ψ) := by
      apply (positiveContinuousMapRiesz_mutuallySingular_iff e |ψ| he (abs_nonneg ψ)).mpr
      rw [inf_comm]
      exact hψe
    rw [haφ]
    apply (positiveContinuousMapRiesz_mutuallySingular_iff φ |ψ| hφ (abs_nonneg ψ)).mp
    exact hsing.mono_ac hAC Measure.AbsolutelyContinuous.rfl

theorem positiveContinuousMap_principalBand_density
    (φ e : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) (he : 0 ≤ e)
    (hband : φ ∈ principalBand e) :
    ∃ f : Lp ℝ 1 (positiveContinuousMapRiesz e he), 0 ≤ f ∧
      continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) f = φ ∧
      ‖f‖ = ‖φ‖ :=
  positiveContinuousMap_density_representation _ φ hφ
    ((positiveContinuousMap_mem_principalBand_iff φ e hφ he).mp hband)

/-- Every real band functional has an actual norm-preserving density. This
statement does not assert uniqueness or assume a band representation. -/
theorem continuousMap_principalBand_density
    (φ e : C(K, ℝ) →L[ℝ] ℝ) (he : 0 ≤ e) (hband : φ ∈ principalBand e) :
    ∃ f : Lp ℝ 1 (positiveContinuousMapRiesz e he),
      continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) f = φ ∧
      ‖f‖ = ‖φ‖ := by
  obtain ⟨f, _, hf, hfn⟩ := positiveContinuousMap_principalBand_density
    φ⁺ e (posPart_nonneg φ) he ((principalBand_orderClosed e).posPart_mem hband)
  obtain ⟨g, _, hg, hgn⟩ := positiveContinuousMap_principalBand_density
    φ⁻ e (negPart_nonneg φ) he ((principalBand_orderClosed e).negPart_mem hband)
  have hmap : continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) (f-g) = φ := by
    rw [map_sub, hf, hg, posPart_sub_negPart]
  refine ⟨f-g, hmap, le_antisymm ?_ ?_⟩
  · calc
      ‖f-g‖ ≤ ‖f‖ + ‖g‖ := norm_sub_le _ _
      _ = ‖φ⁺‖ + ‖φ⁻‖ := by rw [hfn, hgn]
      _ = ‖φ⁺ + φ⁻‖ := (continuousMapDual_norm_add_of_nonneg _ _
        (posPart_nonneg φ) (negPart_nonneg φ)).symm
      _ = ‖φ‖ := by rw [posPart_add_negPart, norm_abs_eq_norm]
  · rw [← hmap]
    exact norm_continuousMapL1Density_le _ _

end ThesisCommon
