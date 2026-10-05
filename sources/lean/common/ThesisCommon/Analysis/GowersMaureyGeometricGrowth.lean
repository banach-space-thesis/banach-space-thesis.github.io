import ThesisCommon.Analysis.GowersMaureyLogGrowth
import Mathlib.Analysis.SpecificLimits.Normed

/-! The logarithmic lower estimate eventually dominates every fixed loss
in a recursively grouped block family. -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon.GowersMaurey

theorem tendsto_logarithmicWeight_pow_div_pow {m c : ℝ} (hm : 1 ≤ m) (hc : 1 < c) :
    Tendsto (fun k : ℕ => logarithmicWeight (m ^ k) / c ^ k) atTop (𝓝 0) := by
  have hzero : Tendsto (fun k : ℕ => 1 / c ^ k) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 0 hc
  have hone : Tendsto (fun k : ℕ => (k : ℝ) / c ^ k) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 hc
  have hupper : Tendsto (fun k : ℕ => 1 / c ^ k +
      ((k : ℝ) / c ^ k) * (Real.log m / Real.log 2)) atTop (𝓝 0) := by
    simpa using hzero.add (hone.mul_const (Real.log m / Real.log 2))
  apply squeeze_zero (fun k => ?_) (fun k => ?_) hupper
  · exact div_nonneg (div_nonneg (Real.log_nonneg (by have : 1 ≤ m ^ k := one_le_pow₀ hm; linarith))
      (Real.log_nonneg (by norm_num))) (pow_nonneg (zero_lt_one.trans hc).le k)
  · have hh := div_le_div_of_nonneg_right (logarithmicWeight_le_log_bound (show 1 ≤ m ^ k from one_le_pow₀ hm))
      (pow_nonneg (zero_lt_one.trans hc).le k)
    rw [Real.log_pow] at hh
    convert hh using 1
    ring

theorem exists_logarithmicWeight_pow_lt {m c : ℝ} (hm : 1 ≤ m) (hc : 1 < c) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ logarithmicWeight (m ^ k) < c ^ k := by
  have hlim := tendsto_logarithmicWeight_pow_div_pow hm hc
  have hsmall : ∀ᶠ k : ℕ in atTop, logarithmicWeight (m ^ k) / c ^ k < 1 :=
    (tendsto_order.mp hlim).2 1 zero_lt_one
  obtain ⟨k, hk, hK⟩ := (hsmall.and (eventually_ge_atTop K)).exists
  exact ⟨k, hK, (div_lt_one (pow_pos (zero_lt_one.trans hc) k)).mp hk⟩

end ThesisCommon.GowersMaurey
