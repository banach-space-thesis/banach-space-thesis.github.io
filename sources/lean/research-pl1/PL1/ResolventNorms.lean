import PL1.TruncatedResolventFactorization
import PL1.WalshBlocks

/-! # Exact norms of the actual resolvents and time cutoffs -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.Noise
open Walsh WalshBlocks

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

theorem norm_resolventL1_eq_one (t : PositiveTime) : ‖resolventL1 𝕜 rates t‖ = 1 := by
  apply le_antisymm (norm_resolventL1_le_one 𝕜 rates t)
  have hf : scalarCharacterLp 𝕜 1 ∅ ≠ 0 := (linearIndependent_characterL1 𝕜).ne_zero ∅
  have hn := (resolventL1 𝕜 rates t).le_opNorm (scalarCharacterLp 𝕜 1 ∅)
  simp only [resolventL1_scalarCharacter, rateSum, Finset.sum_empty, mul_zero,
    add_zero, inv_one, RCLike.ofReal_one, one_smul] at hn
  nlinarith [norm_pos_iff.mpr hf]

theorem norm_noiseL1_eq_one (u : ℝ≥0) : ‖noiseL1 𝕜 rates u‖ = 1 := by
  apply le_antisymm (norm_noiseL1_le_one 𝕜 rates u)
  have hf : scalarCharacterLp 𝕜 1 ∅ ≠ 0 := (linearIndependent_characterL1 𝕜).ne_zero ∅
  have hn := (noiseL1 𝕜 rates u).le_opNorm (scalarCharacterLp 𝕜 1 ∅)
  simp only [noiseL1_character, rateSum, Finset.sum_empty, mul_zero,
    Real.exp_zero, RCLike.ofReal_one, one_smul] at hn
  nlinarith [norm_pos_iff.mpr hf]

theorem norm_truncatedResolventL1_eq (t : PositiveTime) (ε : ℝ≥0) :
    ‖truncatedResolventL1 𝕜 rates t ε‖ = Real.exp (-(ε : ℝ) / (t : ℝ)) := by
  apply le_antisymm
  · rw [truncatedResolventL1_eq_resolvent_comp_noise, norm_smul,
      RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]
    have hb := ContinuousLinearMap.opNorm_comp_le
      (resolventL1 𝕜 rates t) (noiseL1 𝕜 rates ε)
    rw [norm_resolventL1_eq_one, norm_noiseL1_eq_one, mul_one] at hb
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
  · have hf : scalarCharacterLp 𝕜 1 ∅ ≠ 0 := (linearIndependent_characterL1 𝕜).ne_zero ∅
    have he : truncatedResolventL1 𝕜 rates t ε (scalarCharacterLp 𝕜 1 ∅) =
        ((Real.exp (-(ε : ℝ) / (t : ℝ)) : ℝ) : 𝕜) • scalarCharacterLp 𝕜 1 ∅ := by
      rw [truncatedResolventL1_eq_resolvent_comp_noise]
      simp only [smul_apply, ContinuousLinearMap.comp_apply, noiseL1_character,
        resolventL1_scalarCharacter, rateSum, Finset.sum_empty, mul_zero,
        Real.exp_zero, add_zero, inv_one, RCLike.ofReal_one, one_smul]
    have hn := (truncatedResolventL1 𝕜 rates t ε).le_opNorm (scalarCharacterLp 𝕜 1 ∅)
    rw [he, norm_smul, RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)] at hn
    nlinarith [norm_pos_iff.mpr hf]

theorem norm_resolventL1_sub_truncated_eq (t : PositiveTime) (ε : ℝ≥0) :
    ‖resolventL1 𝕜 rates t - truncatedResolventL1 𝕜 rates t ε‖ =
      1 - Real.exp (-(ε : ℝ) / (t : ℝ)) := by
  apply le_antisymm (norm_resolventL1_sub_truncated_le 𝕜 rates t ε)
  have hf : scalarCharacterLp 𝕜 1 ∅ ≠ 0 := (linearIndependent_characterL1 𝕜).ne_zero ∅
  have hnonneg : 0 ≤ 1 - Real.exp (-(ε : ℝ) / (t : ℝ)) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ε.coe_nonneg) t.property.le
  have he : (resolventL1 𝕜 rates t - truncatedResolventL1 𝕜 rates t ε)
      (scalarCharacterLp 𝕜 1 ∅) =
      (((1 - Real.exp (-(ε : ℝ) / (t : ℝ))) : ℝ) : 𝕜) • scalarCharacterLp 𝕜 1 ∅ := by
    rw [truncatedResolventL1_eq_resolvent_comp_noise]
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      noiseL1_character, resolventL1_scalarCharacter, rateSum,
      Finset.sum_empty, mul_zero, Real.exp_zero, add_zero, inv_one,
      RCLike.ofReal_one, one_smul, RCLike.ofReal_sub, sub_smul]
  have hn := (resolventL1 𝕜 rates t - truncatedResolventL1 𝕜 rates t ε).le_opNorm
    (scalarCharacterLp 𝕜 1 ∅)
  rw [he, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hnonneg] at hn
  nlinarith [norm_pos_iff.mpr hf]

end PL1.Noise
