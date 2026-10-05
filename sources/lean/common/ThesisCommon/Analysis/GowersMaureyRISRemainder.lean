import ThesisCommon.Analysis.GowersMaureyRISCutoff
import ThesisCommon.Analysis.GowersMaureyLogGrowth
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The finite remainder in the source's Lemma 7 is controlled by the
literal RIS first-size condition. No asymptotic choice is added to RIS. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem risFormCutoff_ge_square_ratio {N : ℕ} {ε : ℝ}
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (N : ℝ)^2 / ε^2 ≤ risFormCutoff N ε := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : (1 : ℝ) ≤ (N : ℝ)^2 / ε^2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hε)]
    nlinarith
  have hh := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num) hr
  norm_num only [mul_one, one_add_one_eq_two] at hh
  dsimp [risFormCutoff]
  linarith

theorem RISData.size_remainder_budget {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (hN : 2 ≤ N) (i : Fin N) :
    3 * (N : ℝ)^2 < ε * h.size i := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hq : 0 ≤ (N : ℝ)^2 / ε^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hqK := risFormCutoff_ge_square_ratio (by omega : 0 < N) h.epsilon_pos h.epsilon_le_one
  have hn := h.first_large i
  change (4 * N * Real.log 2) * risFormCutoff N ε < h.size i at hn
  have hs : 2 * (N : ℝ) * ((N : ℝ)^2 / ε^2) < h.size i := by
    calc
      _ ≤ (4 * N * Real.log 2) * ((N : ℝ)^2 / ε^2) := by
        apply mul_le_mul_of_nonneg_right _ hq
        nlinarith
      _ ≤ (4 * N * Real.log 2) * risFormCutoff N ε :=
        mul_le_mul_of_nonneg_left hqK (by positivity)
      _ < _ := hn
  rw [← mul_div_assoc, div_lt_iff₀ (sq_pos_of_pos h.epsilon_pos)] at hs
  have hs0 : (0 : ℝ) ≤ h.size i := Nat.cast_nonneg _
  have hepssq : ε^2 ≤ ε := by nlinarith [h.epsilon_pos, h.epsilon_le_one]
  have heps := mul_le_mul_of_nonneg_left hepssq hs0
  nlinarith [mul_nonneg (show 0 ≤ 2 * (N : ℝ) - 3 by linarith) (sq_nonneg (N : ℝ))]

theorem RISData.normalized_interval_remainder_le
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (hN : 2 ≤ N)
    {n : ℕ} (hn : n ≤ N) (i : Fin N) :
    (1 + 2 * ε) * n * logarithmicWeight N / h.size i ≤ ε := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hfn := (logarithmicWeight_lt_self hNr).le
  have hfn0 : 0 ≤ logarithmicWeight N := zero_le_one.trans
    (one_le_logarithmicWeight (by omega))
  have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hC : 0 ≤ 1 + 2 * ε := by linarith [h.epsilon_pos]
  have hnN : (n : ℝ) * logarithmicWeight N ≤ (N : ℝ)^2 := by
    simpa only [pow_two] using mul_le_mul hnn hfn hfn0 (Nat.cast_nonneg N)
  apply (div_le_iff₀ (by exact_mod_cast h.size_pos i : (0 : ℝ) < h.size i)).mpr
  have hbudget := (h.size_remainder_budget hN i).le
  calc
    (1 + 2 * ε) * n * logarithmicWeight N =
        (1 + 2 * ε) * ((n : ℝ) * logarithmicWeight N) := by ring
    _ ≤ (1 + 2 * ε) * (N : ℝ)^2 := mul_le_mul_of_nonneg_left hnN hC
    _ ≤ 3 * (N : ℝ)^2 := by nlinarith [sq_nonneg (N : ℝ), h.epsilon_le_one]
    _ ≤ ε * h.size i := hbudget

end ThesisCommon.GowersMaurey
