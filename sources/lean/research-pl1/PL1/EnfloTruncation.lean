import PL1.EnfloMajorant
import PL1.LpInterpolation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Finite L1 family truncation under a common integrable majorant -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace PL1.EnfloBush

def truncate (M z : ℝ) : ℝ := max (-M) (min M z)

theorem truncate_eq_of_le (M z : ℝ) (hz : |z| ≤ M) : truncate M z = z := by
  obtain ⟨hl, hu⟩ := abs_le.mp hz
  rw [truncate, min_eq_right hu, max_eq_right hl]

theorem abs_truncate_le (M z : ℝ) (hM : 0 ≤ M) : |truncate M z| ≤ M := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem abs_sub_truncate (M z : ℝ) (hM : 0 ≤ M) :
    |z - truncate M z| = max (|z| - M) 0 := by
  by_cases hp : M < z
  · have hz : 0 ≤ z := hM.trans hp.le
    rw [truncate, min_eq_left hp.le, max_eq_right (by linarith : -M ≤ M),
      abs_of_nonneg (sub_nonneg.mpr hp.le), abs_of_nonneg hz,
      max_eq_left (sub_nonneg.mpr hp.le)]
  · by_cases hn : z < -M
    · have hz : z ≤ 0 := hn.le.trans (by linarith)
      rw [truncate, min_eq_right (by linarith : z ≤ M), max_eq_left hn.le,
        abs_of_nonpos (by linarith : z - -M ≤ 0), abs_of_nonpos hz,
        max_eq_left (by linarith : 0 ≤ -z - M)]
      ring
    · have hz : |z| ≤ M := abs_le.mpr ⟨le_of_not_gt hn, le_of_not_gt hp⟩
      rw [truncate_eq_of_le M z hz, sub_self, abs_zero, max_eq_right (sub_nonpos.mpr hz)]

theorem abs_truncate_le_abs (M z : ℝ) (hM : 0 ≤ M) : |truncate M z| ≤ |z| := by
  by_cases hz : |z| ≤ M
  · rw [truncate_eq_of_le M z hz]
  · exact (abs_truncate_le M z hM).trans (le_of_lt (lt_of_not_ge hz))

theorem abs_sub_truncate_le (M z : ℝ) (hM : 0 ≤ M) : |z - truncate M z| ≤ |z| := by
  rw [abs_sub_truncate M z hM]
  exact max_le (by linarith) (abs_nonneg _)

theorem tail_add_le {M a b : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a - M) 0 + max (b - M) 0 ≤ max (a + b - M) 0 := by
  by_cases haM : a ≤ M <;> by_cases hbM : b ≤ M
  · rw [max_eq_right (sub_nonpos.mpr haM), max_eq_right (sub_nonpos.mpr hbM)]
    simpa only [zero_add] using le_max_right (a + b - M) 0
  · rw [max_eq_right (sub_nonpos.mpr haM), max_eq_left (by linarith : 0 ≤ b - M), zero_add]
    exact (by linarith : b - M ≤ a + b - M).trans (le_max_left _ _)
  · rw [max_eq_left (by linarith : 0 ≤ a - M), max_eq_right (sub_nonpos.mpr hbM), add_zero]
    exact (by linarith : a - M ≤ a + b - M).trans (le_max_left _ _)
  · rw [max_eq_left (by linarith : 0 ≤ a - M), max_eq_left (by linarith : 0 ≤ b - M)]
    exact (by linarith : a - M + (b - M) ≤ a + b - M).trans (le_max_left _ _)

theorem sum_truncation_error_le (n : ℕ) (a : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M) :
    (∑ j ∈ Finset.range n, |a j - truncate M (a j)|) ≤
      max ((∑ j ∈ Finset.range n, |a j|) - M) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, abs_sub_truncate M (a n) hM]
    exact (add_le_add ih le_rfl).trans
      (tail_add_le hM (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (abs_nonneg _))

section L1
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_truncate (M : ℝ) (hM : 0 ≤ M) (f : Lp ℝ 1 μ) :
    Integrable (fun x => truncate M (f x)) μ := by
  apply (L1.integrable_coeFn f).mono
  · exact aestronglyMeasurable_const.sup (aestronglyMeasurable_const.inf (Lp.aestronglyMeasurable f))
  · exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using abs_truncate_le_abs M (f x) hM)

def truncateLp (M : ℝ) (hM : 0 ≤ M) (f : Lp ℝ 1 μ) : Lp ℝ 1 μ :=
  (integrable_truncate M hM f).toL1 (fun x => truncate M (f x))

theorem truncateLp_coe (M : ℝ) (hM : 0 ≤ M) (f : Lp ℝ 1 μ) :
    truncateLp M hM f =ᵐ[μ] (fun x => truncate M (f x)) :=
  (integrable_truncate M hM f).coeFn_toL1

theorem truncateLp_bound (M : ℝ) (hM : 0 ≤ M) (f : Lp ℝ 1 μ) :
    ∀ᵐ x ∂μ, ‖truncateLp M hM f x‖ ≤ M := by
  filter_upwards [truncateLp_coe M hM f] with x hx
  rw [hx, Real.norm_eq_abs]
  exact abs_truncate_le M (f x) hM

theorem norm_truncateLp_le (M : ℝ) (hM : 0 ≤ M) (f : Lp ℝ 1 μ) :
    ‖truncateLp M hM f‖ ≤ ‖f‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  apply integral_mono_ae (L1.integrable_coeFn _).norm (L1.integrable_coeFn _).norm
  filter_upwards [truncateLp_coe M hM f] with x hx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_truncate_le_abs M (f x) hM

theorem sum_norm_truncation_error_le (n : ℕ) (f : ℕ → Lp ℝ 1 μ)
    (M : ℝ) (hM : 0 ≤ M) (g : Ω → ℝ) (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x)
    (hfg : ∀ᵐ x ∂μ, (∑ j ∈ Finset.range n, |f j x|) ≤ g x) :
    (∑ j ∈ Finset.range n, ‖f j - truncateLp M hM (f j)‖) ≤
      ∫ x, max (g x - M) 0 ∂μ := by
  have hgI : Integrable (fun x => max (g x - M) 0) μ := by
    apply hg.mono'
    · exact (hg.aestronglyMeasurable.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (hg0 x))
  have he (j : ℕ) : ‖f j - truncateLp M hM (f j)‖ = ∫ x, |f j x - truncate M (f j x)| ∂μ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f j) (truncateLp M hM (f j)), truncateLp_coe M hM (f j)] with x hx ht
    rw [hx, Pi.sub_apply, ht, Real.norm_eq_abs]
  simp_rw [he]
  have herr (j : ℕ) : Integrable (fun x => |f j x - truncate M (f j x)|) μ := by
    simpa only [Pi.sub_apply] using ((L1.integrable_coeFn (f j)).sub
      (integrable_truncate M hM (f j))).abs
  rw [← integral_finsetSum _ (fun j _ => herr j)]
  apply integral_mono_ae (integrable_finsetSum _ (fun j _ => herr j)) hgI
  filter_upwards [hfg] with x hx
  exact (sum_truncation_error_le n (fun j => f j x) hM).trans (max_le_max (sub_le_sub_right hx M) le_rfl)

theorem integral_tail_tendsto_zero (g : Ω → ℝ) (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x) :
    Tendsto (fun n : ℕ => ∫ x, max (g x - (n : ℝ)) 0 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence g
    (fun n => (hg.aestronglyMeasurable.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const)
    hg (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (sub_le_self _ (Nat.cast_nonneg n)) (hg0 x)))
    (Filter.Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      obtain ⟨N, hN⟩ := exists_nat_ge (g x)
      filter_upwards [eventually_ge_atTop N] with n hn
      have he : g x ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
      exact (max_eq_right (sub_nonpos.mpr he)).symm))
  simpa only [integral_zero, Pi.sup_apply, Pi.sub_apply] using h

end L1

#print axioms sum_norm_truncation_error_le
#print axioms integral_tail_tendsto_zero
end PL1.EnfloBush
