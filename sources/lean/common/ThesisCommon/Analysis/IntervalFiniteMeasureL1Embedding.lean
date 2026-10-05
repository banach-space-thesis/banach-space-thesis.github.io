import ThesisCommon.Analysis.IntervalProbabilityL1Retraction
import ThesisCommon.Analysis.IntervalL1SubtypeEquiv
import ThesisCommon.Analysis.LebesgueLpMeasureScale

/-! Every finite Borel measure on the interval has L1 isometrically and
contractively complemented in actual Lebesgue L1[0,1]. The maps are obtained
by measure normalization, inverse-CDF sampling, and conditional integration.
The zero measure is handled explicitly. No fibre classification is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]
variable (μ : Measure UnitInterval) [IsFiniteMeasure μ]

theorem exists_intervalFiniteMeasureL1_retraction :
    ∃ (J : Lp 𝕜 1 μ →ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩)
      (R : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ),
      ‖R‖ ≤ 1 ∧ R.comp J.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 μ) := by
  by_cases hμ : μ = 0
  · subst μ
    letI : Subsingleton (Lp 𝕜 1 (0 : Measure UnitInterval)) :=
      ⟨fun f g => Lp.ext (by simp only [ae_zero]; exact Filter.eventually_bot)⟩
    let J : Lp 𝕜 1 (0 : Measure UnitInterval) →ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
      { toLinearMap := 0
        norm_map' := fun x => by simp [Subsingleton.elim x 0] }
    refine ⟨J, 0, by simp, ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  · letI : NeZero μ := ⟨hμ⟩
    let ν := (μ univ)⁻¹ • μ
    have hm0 : μ univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.mp h)
    have hmtop : μ univ ≠ ∞ := measure_ne_top μ univ
    let e : Lp 𝕜 1 μ ≃ₗᵢ[𝕜] Lp 𝕜 1 ν :=
      (lebesgueLpMeasureScaleEquiv (𝕜 := 𝕜) (E := 𝕜) (μ := μ) (p := 1)
        (by simp) (μ univ)⁻¹ (ENNReal.inv_ne_zero.mpr hmtop) (ENNReal.inv_ne_top.mpr hm0)).symm
    let b := IntervalL1Subtype.equiv 𝕜
    let J : Lp 𝕜 1 μ →ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
      b.toLinearIsometry.comp
        ((IntervalL1Retraction.pullback (𝕜 := 𝕜) ν).comp e.toLinearIsometry)
    let R : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ :=
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((IntervalL1Retraction.retraction (𝕜 := 𝕜) ν).comp
          b.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    refine ⟨J, R, ?_, ?_⟩
    · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      change ‖e.symm (IntervalL1Retraction.retraction ν (b.symm x))‖ ≤ 1 * ‖x‖
      rw [e.symm.norm_map, one_mul]
      calc
        _ ≤ ‖IntervalL1Retraction.retraction (𝕜 := 𝕜) ν‖ * ‖b.symm x‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖b.symm x‖ := mul_le_mul_of_nonneg_right
          (IntervalL1Retraction.norm_retraction_le ν) (norm_nonneg _)
        _ = ‖x‖ := by rw [one_mul, b.symm.norm_map]
    · apply ContinuousLinearMap.ext
      intro x
      change e.symm (IntervalL1Retraction.retraction ν
        (b.symm (b (IntervalL1Retraction.pullback ν (e x))))) = x
      rw [b.symm_apply_apply, IntervalL1Retraction.retraction_pullback, e.symm_apply_apply]

end ThesisCommon
