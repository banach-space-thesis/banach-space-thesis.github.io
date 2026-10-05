import ThesisCommon.Analysis.GowersMaureyLogGrowth

/-! Fixed multiplicative changes of scale do not change the asymptotic
size of the actual logarithmic weight log₂(r+1). -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon.GowersMaurey

theorem tendsto_log_scaled_one_sub_log_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => Real.log (c*r+1) - Real.log (r+1)) atTop (𝓝 (Real.log c)) := by
  have h := ((Real.tendsto_log_comp_add_sub_log (1/c)).sub
    (Real.tendsto_log_comp_add_sub_log 1)).add (tendsto_const_nhds (x := Real.log c))
  simp only [sub_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r + 1/c := by positivity
  have he : c*r+1 = c*(r+1/c) := by field_simp
  rw [he, Real.log_mul hc.ne' hr0.ne']
  ring

theorem tendsto_logarithmicWeight_div_scaled {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => logarithmicWeight r / logarithmicWeight (c*r))
      atTop (𝓝 1) := by
  have harg : Tendsto (fun r : ℝ => c*r+1) atTop atTop :=
    (tendsto_id.const_mul_atTop hc).atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hden := Real.tendsto_log_atTop.comp harg
  have hd := (tendsto_log_scaled_one_sub_log_one hc).div_atTop hden
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hd
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [hden.eventually (eventually_gt_atTop (0 : ℝ))] with r hr
  dsimp only [Function.comp_apply] at hr ⊢
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold logarithmicWeight
  field_simp [hr.ne', h2]
  ring

theorem eventually_logarithmicWeight_le_one_add_mul_scaled
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in atTop, logarithmicWeight r ≤ (1+δ) * logarithmicWeight (c*r) := by
  have hratio := (tendsto_logarithmicWeight_div_scaled hc).eventually_le_const
    (show (1 : ℝ) < 1+δ by linarith)
  have hden := tendsto_logarithmicWeight_atTop.comp (tendsto_id.const_mul_atTop hc)
  filter_upwards [hratio, hden.eventually (eventually_gt_atTop (0 : ℝ))] with r hr hpos
  exact (div_le_iff₀ hpos).mp hr

theorem eventually_logarithmicWeight_le_one_add_mul_div
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    ∀ᶠ r : ℝ in atTop, logarithmicWeight r ≤ (1+δ) * logarithmicWeight (r/n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
    eventually_logarithmicWeight_le_one_add_mul_scaled (c := 1/(n : ℝ)) (by positivity) hδ

theorem logarithmicWeight_nat_le_one_add_mul_div
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      logarithmicWeight r ≤ (1+δ) * logarithmicWeight ((r : ℝ)/n) :=
  eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually
    (eventually_logarithmicWeight_le_one_add_mul_div hδ hn))

end ThesisCommon.GowersMaurey
