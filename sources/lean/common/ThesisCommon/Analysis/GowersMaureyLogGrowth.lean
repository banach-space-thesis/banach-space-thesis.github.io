import ThesisCommon.Analysis.GowersMaureyFiniteSequences
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Growth properties of the actual fixed profile log₂(x+1). In particular
its ratio to every positive real power tends to zero, with a natural-index
eventual bound for the block-average arguments. -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon.GowersMaurey

theorem logarithmicWeight_strictMonoOn : StrictMonoOn logarithmicWeight (Set.Ici 1) := by
  intro x hx y hy hxy
  unfold logarithmicWeight
  exact (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num))).mpr
    (Real.log_lt_log (by change 1 ≤ x at hx; linarith) (by linarith))

theorem logarithmicWeight_lt_self {x : ℝ} (hx : 1 < x) : logarithmicWeight x < x := by
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have hh := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
    rw [Real.log_inv] at hh
    norm_num at hh
    linarith
  have hb := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / 2 by linarith)
  rw [Real.log_div (by linarith : x + 1 ≠ 0) (by norm_num)] at hb
  unfold logarithmicWeight
  apply (div_lt_iff₀ (Real.log_pos (by norm_num))).mpr
  nlinarith [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hlog2)]

theorem tendsto_logarithmicWeight_atTop : Tendsto logarithmicWeight atTop atTop :=
  Tendsto.atTop_div_const (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (Real.tendsto_log_atTop.comp (tendsto_id.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))))

theorem logarithmicWeight_le_log_bound {x : ℝ} (hx : 1 ≤ x) :
    logarithmicWeight x ≤ 1 + Real.log x / Real.log 2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hh := Real.log_le_log (by linarith : 0 < x + 1) (by linarith : x + 1 ≤ 2 * x)
  rw [Real.log_mul (by norm_num) hx0.ne'] at hh
  unfold logarithmicWeight
  apply (div_le_iff₀ (Real.log_pos (by norm_num))).mpr
  have heq : (1 + Real.log x / Real.log 2) * Real.log 2 = Real.log 2 + Real.log x := by
    field_simp
  rwa [heq]

theorem tendsto_logarithmicWeight_div_rpow {q : ℝ} (hq : 0 < q) :
    Tendsto (fun x : ℝ => logarithmicWeight x / x ^ q) atTop (𝓝 0) := by
  have hlog := (isLittleO_log_rpow_atTop hq).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => 1 / x ^ q) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hq)
  have hupper : Tendsto (fun x : ℝ => 1 / x ^ q +
      (Real.log x / x ^ q) / Real.log 2) atTop (𝓝 0) := by
    simpa using hinv.add (hlog.div_const (Real.log 2))
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (div_nonneg (Real.log_nonneg (by linarith))
      (Real.log_nonneg (by norm_num))) (Real.rpow_nonneg (by linarith) _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hh := div_le_div_of_nonneg_right (logarithmicWeight_le_log_bound hx)
      (Real.rpow_nonneg (by linarith : 0 ≤ x) q)
    convert hh using 1 <;> ring

theorem tendsto_logarithmicWeight_nat_div_rpow {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n : ℕ => logarithmicWeight n / (n : ℝ) ^ q) atTop (𝓝 0) :=
  (tendsto_logarithmicWeight_div_rpow hq).comp tendsto_natCast_atTop_atTop

theorem logarithmicWeight_nat_subpower {q : ℝ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → logarithmicWeight n < ε * (n : ℝ) ^ q := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_logarithmicWeight_nat_div_rpow hq) ε hε
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hr : 0 < (n : ℝ) ^ q := Real.rpow_pos_of_pos hnp q
  have hh := hN n ((le_max_left N 1).trans hn)
  have hsmall : logarithmicWeight n / (n : ℝ) ^ q < ε := by
    exact (abs_lt.mp (by simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hh)).2
  exact (div_lt_iff₀ hr).mp hsmall

end ThesisCommon.GowersMaurey
