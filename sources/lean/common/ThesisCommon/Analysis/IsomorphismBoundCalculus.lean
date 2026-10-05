import ThesisCommon.Analysis.BoundedEquivalenceCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Attained distortion bounds and rescaling of actual bounded equivalences.
These are the elementary quantitative operations used in Appendix A. The
zero-space case is handled without dividing by a zero operator norm. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem IsomorphicWithBound.symm {C : ℝ} (h : IsomorphicWithBound 𝕜 X Y C) :
    IsomorphicWithBound 𝕜 Y X C := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by simpa only [ContinuousLinearEquiv.symm_symm, mul_comm] using he⟩

theorem IsomorphicWithBound.mono {C D : ℝ} (h : IsomorphicWithBound 𝕜 X Y C)
    (hCD : C ≤ D) : IsomorphicWithBound 𝕜 X Y D := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, he.trans hCD⟩

theorem IsomorphicWithBound.trans {C D : ℝ} (h : IsomorphicWithBound 𝕜 X Y C)
    (hf : IsomorphicWithBound 𝕜 Y Z D) : IsomorphicWithBound 𝕜 X Z (C * D) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := hf
  have hC : 0 ≤ C := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans he
  refine ⟨e.trans f, ?_⟩
  calc
    _ ≤ (‖f.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖) *
        (‖e.symm.toContinuousLinearMap‖ * ‖f.symm.toContinuousLinearMap‖) :=
      mul_le_mul (f.toContinuousLinearMap.opNorm_comp_le e.toContinuousLinearMap)
        (e.symm.toContinuousLinearMap.opNorm_comp_le f.symm.toContinuousLinearMap)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) *
        (‖f.toContinuousLinearMap‖ * ‖f.symm.toContinuousLinearMap‖) := by ring
    _ ≤ C * D := mul_le_mul he hf (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC

def scaledContinuousLinearEquiv (a : 𝕜) (ha : a ≠ 0) (e : X ≃L[𝕜] Y) : X ≃L[𝕜] Y :=
  ContinuousLinearEquiv.equivOfInverse (a • e.toContinuousLinearMap)
    (a⁻¹ • e.symm.toContinuousLinearMap)
    (by
      intro x
      change a⁻¹ • e.symm (a • e x) = x
      rw [map_smul, smul_smul, inv_mul_cancel₀ ha, one_smul, e.symm_apply_apply])
    (by
      intro y
      change a • e (a⁻¹ • e.symm y) = y
      rw [map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul, e.apply_symm_apply])

/-- A distortion bound C≥1 admits a rescaled equivalence whose forward
and inverse norms are both at most √C, including the zero-space case. -/
theorem IsomorphicWithBound.exists_sqrt_normBound {C : ℝ}
    (h : IsomorphicWithBound 𝕜 X Y C) (hC : 1 ≤ C) :
    ∃ e : X ≃L[𝕜] Y, EquivNormBound e (Real.sqrt C) := by
  obtain ⟨e, he⟩ := h
  rcases subsingleton_or_nontrivial X with hX | hX
  · letI := hX
    refine ⟨e, ?_, ?_⟩
    · intro x
      simp only [Subsingleton.elim x 0, map_zero, norm_zero, mul_zero, le_refl]
    · intro y
      rw [Subsingleton.elim (e.symm y) 0, norm_zero]
      positivity
  · letI := hX
    have hepos : 0 < ‖e.toContinuousLinearMap‖ := e.norm_pos
    have hspos : 0 < Real.sqrt C := Real.sqrt_pos.2 (zero_lt_one.trans_le hC)
    let a : ℝ := Real.sqrt C / ‖e.toContinuousLinearMap‖
    have ha : 0 < a := div_pos hspos hepos
    have hnorma : ‖(a : 𝕜)‖ = a := by rw [RCLike.norm_ofReal, abs_of_pos ha]
    have ha0 : (a : 𝕜) ≠ 0 := by
      apply norm_pos_iff.mp
      rwa [hnorma]
    have hleft : a * ‖e.toContinuousLinearMap‖ = Real.sqrt C :=
      div_mul_cancel₀ _ hepos.ne'
    have hright : a⁻¹ * ‖e.symm.toContinuousLinearMap‖ ≤ Real.sqrt C := by
      rw [inv_mul_eq_div, div_le_iff₀ ha]
      dsimp [a]
      rw [← mul_div_assoc, le_div_iff₀ hepos]
      nlinarith [Real.sq_sqrt (zero_le_one.trans hC)]
    refine ⟨scaledContinuousLinearEquiv (a : 𝕜) ha0 e, ?_, ?_⟩
    · intro x
      change ‖(a : 𝕜) • e x‖ ≤ Real.sqrt C * ‖x‖
      rw [norm_smul, hnorma]
      calc
        _ ≤ a * (‖e.toContinuousLinearMap‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (e.toContinuousLinearMap.le_opNorm x) ha.le
        _ = Real.sqrt C * ‖x‖ := by rw [← mul_assoc, hleft]
    · intro y
      change ‖(a : 𝕜)⁻¹ • e.symm y‖ ≤ Real.sqrt C * ‖y‖
      rw [norm_smul, norm_inv, hnorma]
      calc
        _ ≤ a⁻¹ * (‖e.symm.toContinuousLinearMap‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left (e.symm.toContinuousLinearMap.le_opNorm y) (inv_nonneg.mpr ha.le)
        _ = (a⁻¹ * ‖e.symm.toContinuousLinearMap‖) * ‖y‖ := by ring
        _ ≤ Real.sqrt C * ‖y‖ := mul_le_mul_of_nonneg_right hright (norm_nonneg y)

end ThesisCommon
