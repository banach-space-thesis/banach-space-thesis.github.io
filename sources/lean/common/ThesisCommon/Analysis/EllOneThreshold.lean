import ThesisCommon.Analysis.CotypeEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The numerical N^(1-1/p) threshold used in the ell1 reductions. -/
noncomputable section
namespace ThesisCommon
open Filter

theorem ellOne_power_threshold {n : ℕ} {q M ε : ℝ} (hq : 1 < q) (hM : 0 ≤ M)
    (hlarge : 2 * M < (n : ℝ) ^ ((q - 1) / q) * ε) :
    M * (n : ℝ) ^ (1 / q) < (n : ℝ) * (ε / 2) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have ha : 0 < (q - 1) / q := div_pos (sub_pos.mpr hq) hq0
  have hn : 0 < n := by
    by_contra! hn
    have hz : n = 0 := by omega
    simp only [hz, Nat.cast_zero, Real.zero_rpow ha.ne', zero_mul] at hlarge
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < (n : ℝ) ^ (1 / q) := Real.rpow_pos_of_pos hn0 _
  have hmul := mul_lt_mul_of_pos_right (show M < (n : ℝ) ^ ((q-1)/q) * (ε/2) by linarith) hr
  have heq : (n : ℝ) ^ ((q-1)/q) * (n : ℝ) ^ (1/q) = n := by
    rw [← Real.rpow_add hn0]
    have hexp : (q-1)/q + 1/q = 1 := by field_simp; ring
    rw [hexp, Real.rpow_one]
  calc
    _ < ((n : ℝ) ^ ((q-1)/q) * (ε/2)) * (n : ℝ) ^ (1/q) := hmul
    _ = ((n : ℝ) ^ ((q-1)/q) * (n : ℝ) ^ (1/q)) * (ε/2) := by ring
    _ = _ := by rw [heq]

theorem exists_ellOne_power_threshold {q M ε : ℝ} (hq : 1 < q) (hε : 0 < ε) :
    ∃ n : ℕ, 2 * M < (n : ℝ) ^ ((q-1)/q) * ε := by
  have ha : 0 < (q-1)/q := div_pos (sub_pos.mpr hq) (zero_lt_one.trans hq)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((q-1)/q)) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_atTop (2 * M / ε))).exists
  exact ⟨n, (div_lt_iff₀ hε).mp hn⟩

end ThesisCommon

