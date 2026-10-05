import Posets.AlspachCounterexampleSynthesis
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Banach

/-! A quantitative lower bound for an adjoint implies surjectivity.
This supplies the functional-analytic step in Alspach (1997), Proposition 2.1.
The geometric-series lifting argument below is adapted from mathlib's
`ContinuousLinearMap.exists_preimage_norm_le`, copyright (c) 2019
Sébastien Gouëzel, Apache 2.0. -/

noncomputable section
open Set Filter Topology Metric
namespace Posets

section Real
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem alspach_mem_closure_image_ball_of_adjoint_lower
    (T : E →L[ℝ] F) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ φ : F →L[ℝ] ℝ, c * ‖φ‖ ≤ ‖φ.comp T‖) (y : F) :
    y ∈ closure (T '' closedBall 0 (‖y‖ / c)) := by
  by_cases hy : y = 0
  · subst y
    exact subset_closure ⟨0, by simp, by simp⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hr : 0 < ‖y‖ / c := div_pos hn hc
  by_contra hyc
  have hconv : Convex ℝ (closure (T '' closedBall 0 (‖y‖ / c))) :=
    ((convex_closedBall (0 : E) (‖y‖ / c)).linear_image T.toLinearMap).closure
  obtain ⟨φ, u, hu, huy⟩ := geometric_hahn_banach_closed_point hconv isClosed_closure hyc
  have hu0 : 0 < u := by
    simpa only [map_zero] using hu 0 (subset_closure ⟨0, by simp [hr.le], by simp⟩)
  have hop : ‖φ.comp T‖ ≤ u / (‖y‖ / c) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hu0.le hr.le)
    intro x hx
    have hp := hu (T ((‖y‖ / c) • x))
      (subset_closure ⟨(‖y‖ / c) • x, by simp [norm_smul, hx, abs_of_pos hc], rfl⟩)
    have hm := hu (T (-(‖y‖ / c) • x))
      (subset_closure ⟨-(‖y‖ / c) • x, by simp [norm_smul, hx, abs_of_pos hc], rfl⟩)
    simp only [map_smul, smul_eq_mul, neg_mul, ContinuousLinearMap.comp_apply] at hp hm ⊢
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hd : -φ (T x) ≤ u / (‖y‖ / c) :=
        (le_div_iff₀ hr).mpr (by nlinarith)
      linarith
    · exact (le_div_iff₀ hr).mpr (by nlinarith)
  have hbound := (hlower φ).trans hop
  have hmul := (le_div_iff₀ hr).mp hbound
  have he : c * ‖φ‖ * (‖y‖ / c) = ‖φ‖ * ‖y‖ := by field_simp
  rw [he] at hmul
  have hφy : φ y ≤ ‖φ‖ * ‖y‖ := (le_abs_self _).trans (φ.le_opNorm y)
  linarith

end Real

section Approximation
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem alspach_surjective_of_approximation (T : E →L[𝕜] F)
    {C : ℝ} (hC : 0 ≤ C)
    (happrox : ∀ y, ∃ x, ‖y - T x‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    Function.Surjective T := by
  choose g hg using happrox
  let h (y : F) := y - T (g y)
  have hle : ∀ y, ‖h y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := fun y => (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ']
        apply (hle _).trans
        rw [pow_succ', mul_assoc]
        exact mul_le_mul_of_nonneg_left ih (by norm_num)
  let u (n : ℕ) := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by
    intro n
    apply (hg _).2.trans
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2 : ℝ) ^ n * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hnle n) hC
      _ = _ := by ring
  have sNu : Summable fun n => ‖u n‖ :=
    .of_nonneg_of_le (fun n => norm_nonneg _) ule
      (Summable.mul_right _ summable_geometric_two)
  have su : Summable u := sNu.of_norm
  have hsum : ∀ n : ℕ, T (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, map_add, ih, Function.iterate_succ_apply']
        dsimp [h, u]
        abel
  have hlim : Tendsto (fun n => T (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (T (∑' n, u n))) :=
    T.continuous.continuousAt.tendsto.comp su.hasSum.tendsto_sum_nat
  simp only [hsum] at hlim
  have hz : Tendsto (fun n => h^[n] y) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero (fun n => norm_nonneg _) hnle
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖y‖
  have he := tendsto_nhds_unique hlim (tendsto_const_nhds.sub hz)
  exact ⟨∑' n, u n, by simpa using he⟩

end Approximation

section RealSurjection
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem alspach_surjective_of_real_adjoint_lower (T : E →L[ℝ] F) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ φ : F →L[ℝ] ℝ, c * ‖φ‖ ≤ ‖φ.comp T‖) : Function.Surjective T := by
  apply alspach_surjective_of_approximation T (C := 1 / c) (by positivity)
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp, by simp⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := Metric.mem_closure_iff.mp
    (alspach_mem_closure_image_ball_of_adjoint_lower T hc hlower y)
      (‖y‖ / 2) (half_pos hn)
  refine ⟨x, ?_, ?_⟩
  · simpa [dist_eq_norm, div_eq_mul_inv, mul_comm] using hxy.le
  · simpa [mem_closedBall, dist_zero_right, div_eq_mul_inv, mul_comm] using hx

end RealSurjection

theorem alspach_surjective_of_adjoint_lower {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ φ : F →L[𝕜] 𝕜, c * ‖φ‖ ≤ ‖φ.comp T‖) : Function.Surjective T := by
  letI : CompleteSpace (RestrictScalars ℝ 𝕜 E) := ‹CompleteSpace E›
  let TC : RestrictScalars ℝ 𝕜 E →L[𝕜] RestrictScalars ℝ 𝕜 F := T
  let TR := TC.restrictScalars ℝ
  apply alspach_surjective_of_real_adjoint_lower TR hc
  intro φ
  have he : (φ.comp TR).extendTo𝕜' = (φ.extendTo𝕜' : _ →L[𝕜] 𝕜).comp TC := by
    ext x
    change (φ (TC x) : 𝕜) - RCLike.I * (φ (TC (RCLike.I • x)) : 𝕜) =
      (φ (TC x) : 𝕜) - RCLike.I * (φ (RCLike.I • TC x) : 𝕜)
    rw [map_smul]
  have hl := hlower (φ.extendTo𝕜' : F →L[𝕜] 𝕜)
  change c * ‖(φ.extendTo𝕜' : _ →L[𝕜] 𝕜)‖ ≤
    ‖(φ.extendTo𝕜' : _ →L[𝕜] 𝕜).comp TC‖ at hl
  rw [← he, ContinuousLinearMap.norm_extendTo𝕜', ContinuousLinearMap.norm_extendTo𝕜'] at hl
  exact hl

end Posets
