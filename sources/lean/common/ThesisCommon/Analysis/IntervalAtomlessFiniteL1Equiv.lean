import ThesisCommon.Analysis.IntervalAtomlessLpEquiv
import ThesisCommon.Analysis.LebesgueLpMeasureScale

/-! Every nonzero atomless finite interval measure has actual L1 linearly
isometric to Lebesgue L1. Explicit measure normalization removes the
probability hypothesis; the zero measure is deliberately excluded. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon

def intervalAtomlessFiniteL1Equiv (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure unitInterval) [IsFiniteMeasure μ] [NoAtoms μ] (hμ : μ ≠ 0) :
    Lp 𝕜 1 μ ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ := by
  letI : NeZero μ := ⟨hμ⟩
  let ν := (μ univ)⁻¹ • μ
  letI : NoAtoms ν := ⟨fun x => by simp [ν, Measure.smul_apply]⟩
  have hm0 : μ univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  have hmtop : μ univ ≠ ∞ := measure_ne_top μ univ
  let e : Lp 𝕜 1 μ ≃ₗᵢ[𝕜] Lp 𝕜 1 ν :=
    (lebesgueLpMeasureScaleEquiv (𝕜 := 𝕜) (E := 𝕜) (μ := μ) (p := 1)
      (by simp) (μ univ)⁻¹ (ENNReal.inv_ne_zero.mpr hmtop)
      (ENNReal.inv_ne_top.mpr hm0)).symm
  exact e.trans (intervalAtomlessProbabilityL1Equiv 𝕜 ν)

theorem exists_intervalAtomlessFiniteL1_equiv (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure unitInterval) [IsFiniteMeasure μ] [NoAtoms μ] (hμ : μ ≠ 0) :
    Nonempty (Lp 𝕜 1 μ ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩) :=
  ⟨intervalAtomlessFiniteL1Equiv 𝕜 μ hμ⟩

end ThesisCommon
