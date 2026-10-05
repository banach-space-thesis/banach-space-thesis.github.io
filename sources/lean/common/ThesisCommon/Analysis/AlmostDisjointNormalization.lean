import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! Quantitative subsequence and normalization tools for almost-disjoint
factorization. The summable subsequence is constructed from convergence,
and normalization is justified by a positive limiting norm. -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon

/-- A nonnegative null sequence has a strictly increasing subsequence with
arbitrarily small sum, while preserving any eventual condition. -/
theorem exists_summable_subsequence_lt {e : ℕ → ℝ}
    (he : ∀ n, 0 ≤ e n) (hlim : Tendsto e atTop (𝓝 0))
    {P : ℕ → Prop} (hP : ∀ᶠ n in atTop, P n) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, P (φ n)) ∧
      Summable (fun n => e (φ n)) ∧ (∑' n, e (φ n)) < ε := by
  have hev (n : ℕ) : ∀ᶠ k in atTop,
      P k ∧ e k < (ε / 4) * (1 / 2 : ℝ) ^ n :=
    hP.and (hlim.eventually (gt_mem_nhds (by positivity)))
  obtain ⟨φ, hφ, hφe⟩ := extraction_forall_of_eventually hev
  have hbound : Summable (fun n : ℕ => (ε / 4) * (1 / 2 : ℝ) ^ n) :=
    summable_geometric_two.mul_left (ε / 4)
  have hsum : Summable (fun n => e (φ n)) :=
    Summable.of_nonneg_of_le (fun n => he _) (fun n => (hφe n).2.le) hbound
  refine ⟨φ, hφ, fun n => (hφe n).1, hsum, ?_⟩
  calc
    (∑' n, e (φ n)) ≤ ∑' n : ℕ, (ε / 4) * (1 / 2 : ℝ) ^ n :=
      hsum.tsum_le_tsum (fun n => (hφe n).2.le) hbound
    _ = ε / 2 := by rw [tsum_mul_left, tsum_geometric_two]; ring
    _ < ε := by linarith

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem tendsto_norm_model_of_norm_error {f g : ℕ → E} {c : ℝ}
    (herr : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0))
    (hf : Tendsto (fun n => ‖f n‖) atTop (𝓝 c)) :
    Tendsto (fun n => ‖g n‖) atTop (𝓝 c) := by
  apply hf.congr_dist
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) herr
  simpa only [Real.dist_eq] using abs_norm_sub_norm_le (f n) (g n)

/-- If a model differs by a norm-null error and the original norms tend to
`c > 0`, then normalizing both to limiting norm one still gives a null error. -/
theorem tendsto_normalized_model_error {f g : ℕ → E} {c : ℝ} (hc : 0 < c)
    (herr : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0))
    (hf : Tendsto (fun n => ‖f n‖) atTop (𝓝 c)) :
    Tendsto (fun n => ‖((c⁻¹ : ℝ) : 𝕜) • f n -
      ((‖g n‖⁻¹ : ℝ) : 𝕜) • g n‖) atTop (𝓝 0) := by
  have hg := tendsto_norm_model_of_norm_error herr hf
  have hi := hg.inv₀ hc.ne'
  have hb : Tendsto (fun n => c⁻¹ * ‖f n - g n‖ +
      |c⁻¹ - ‖g n‖⁻¹| * ‖g n‖) atTop (𝓝 0) := by
    convert (herr.const_mul c⁻¹).add
      (((tendsto_const_nhds.sub hi).abs).mul hg) using 1 <;> simp
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
  have heq : ((c⁻¹ : ℝ) : 𝕜) • f n - ((‖g n‖⁻¹ : ℝ) : 𝕜) • g n =
      ((c⁻¹ : ℝ) : 𝕜) • (f n - g n) +
        ((c⁻¹ - ‖g n‖⁻¹ : ℝ) : 𝕜) • g n := by
    rw [RCLike.ofReal_sub, sub_smul, smul_sub]
    abel
  rw [heq]
  simpa only [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hc)] using
    norm_add_le (((c⁻¹ : ℝ) : 𝕜) • (f n - g n))
      (((c⁻¹ - ‖g n‖⁻¹ : ℝ) : 𝕜) • g n)

end ThesisCommon
