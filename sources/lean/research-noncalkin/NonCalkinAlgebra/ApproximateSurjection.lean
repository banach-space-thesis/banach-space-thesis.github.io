/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in source/mathlib-universal/LICENSE.
The geometric-correction proof below adapts the second half of
ContinuousLinearMap.exists_preimage_norm_le in the pinned mathlib's
Analysis/Normed/Operator/Banach.lean. The original source is preserved there.
-/
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open Filter Topology Function
open scoped BigOperators
universe u v
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Uniform approximate right inverses with contraction factor one half
produce actual bounded preimages. No surjectivity is assumed. -/
theorem exists_preimage_of_approximate_preimage (T : E →L[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (happrox : ∀ y : F, ∃ x : E,
      ‖y - T x‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    ∀ y : F, ∃ x : E, T x = y ∧ ‖x‖ ≤ (2 * C + 1) * ‖y‖ := by
  classical
  choose g hg using happrox
  let h (y : F) := y - T (g y)
  have hle : ∀ y, ‖h y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := fun y => (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n ih =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let a (n : ℕ) := g (h^[n] y)
  have ha : ∀ n : ℕ, ‖a n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖y‖) := fun n => by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2 : ℝ) ^ n * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hnle n) hC
      _ = (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by ring
  have hna : Summable (fun n => ‖a n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ha ?_
    exact Summable.mul_right _ summable_geometric_two
  have hsa : Summable a := hna.of_norm
  have hbound : ‖∑' n, a n‖ ≤ (2 * C + 1) * ‖y‖ := by
    calc
      ‖∑' n, a n‖ ≤ ∑' n, ‖a n‖ := norm_tsum_le_tsum_norm hna
      _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * (C * ‖y‖) :=
        hna.tsum_le_tsum ha (Summable.mul_right _ summable_geometric_two)
      _ = (∑' n, (1 / 2 : ℝ) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ (2 * C + 1) * ‖y‖ := by nlinarith [norm_nonneg y]
  have hpartial : ∀ n : ℕ, T (∑ i ∈ Finset.range n, a i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [T.map_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, T.map_add, ih, iterate_succ_apply', sub_add]
  have hlim₁ : Tendsto (fun n => T (∑ i ∈ Finset.range n, a i)) atTop
      (𝓝 (T (∑' n, a n))) :=
    (T.continuous.tendsto _).comp hsa.hasSum.tendsto_sum_nat
  simp only [hpartial] at hlim₁
  have hlim₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul tendsto_const_nhds
  exact ⟨∑' n, a n, by simpa only [sub_zero] using tendsto_nhds_unique hlim₁ hlim₂, hbound⟩

theorem surjective_of_approximate_preimage (T : E →L[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (happrox : ∀ y : F, ∃ x : E,
      ‖y - T x‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) : Function.Surjective T := by
  intro y
  obtain ⟨x, hx, hnorm⟩ := exists_preimage_of_approximate_preimage T C hC happrox y
  exact ⟨x, hx⟩

end NonCalkinAlgebra
