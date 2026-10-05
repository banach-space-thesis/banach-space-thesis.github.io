import ThesisCommon.Analysis.GowersMaureyRISLargeForms

/-! Numerical consequences of the literal first-size clause of an RIS. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def risFormCutoff (N : ℕ) (ε : ℝ) : ℝ := (2 : ℝ)^((N : ℝ)^2 / ε^2) - 1

theorem risFormCutoff_ge_one {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ risFormCutoff N ε := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : (1 : ℝ) ≤ (N : ℝ)^2 / ε^2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hε)]
    nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr
  norm_num only [Real.rpow_one] at hp
  dsimp [risFormCutoff]
  linarith

theorem RISData.size_ratio_le_one {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (i : Fin N) :
    (N : ℝ) / h.size i ≤ 1 := by
  have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
  have hK := risFormCutoff_ge_one hN h.epsilon_pos h.epsilon_le_one
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hK
    (show 0 ≤ 4 * (N : ℝ) * Real.log 2 by positivity)
  have hn := h.first_large i
  change (4 * N * Real.log 2) * risFormCutoff N ε < h.size i at hn
  apply (div_le_one (by exact_mod_cast h.size_pos i : (0 : ℝ) < h.size i)).mpr
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * (N : ℝ) by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem RISData.small_form_budget {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (i : Fin N) {k : ℕ}
    (hk : (k : ℝ) < risFormCutoff N ε) :
    (k : ℝ) * ((N : ℝ) / h.size i) ≤ 1 / (4 * Real.log 2) := by
  have hn : (0 : ℝ) < h.size i := by exact_mod_cast h.size_pos i
  have hl : 0 < 4 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hfirst := h.first_large i
  change (4 * N * Real.log 2) * risFormCutoff N ε < h.size i at hfirst
  have hprod := mul_le_mul_of_nonneg_left hk.le
    (show 0 ≤ 4 * (N : ℝ) * Real.log 2 by positivity)
  rw [← mul_div_assoc, div_le_div_iff₀ hn hl]
  nlinarith

end ThesisCommon.GowersMaurey
