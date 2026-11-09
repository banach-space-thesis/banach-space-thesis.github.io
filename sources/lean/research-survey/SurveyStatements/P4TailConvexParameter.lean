import SurveyStatements.P4TailConvexScalar
import SurveyStatements.P4TailConvexEvaluation
import SurveyStatements.P4TailConvexMazur
import SurveyStatements.P4TailConvexNorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

/-! Parameter tail convexification from a bounded continuous norm
approximation of the weak pointwise limit. -/

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One common sequence of finite convex tail coefficients gives pointwise
norm convergence on every parameter, without any countability assumption on
the parameter set or on the full dual of E. -/
theorem parameter_tail_convexification_bounded
    (fseq : ℕ → C(K, E)) (C : ℝ) (hbound : ∀ n, ‖fseq n‖ ≤ C)
    (f : K → E)
    (hweak : ∀ t (φ : StrongDual ℝ E),
      Tendsto (fun n => φ (fseq n t)) atTop (𝓝 (φ (f t))))
    (u : ℕ → C(K, E)) (D : ℝ) (hubound : ∀ n, ‖u n‖ ≤ D)
    (hu : ∀ t, Tendsto (fun n => u n t) atTop (𝓝 (f t))) :
    ∃ (F : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ),
      (∀ k n, 0 ≤ a k n) ∧ (∀ k, ∑ n ∈ F k, a k n = 1) ∧
      (∀ k n, n ∈ F k → k ≤ n) ∧
      ∀ t, Tendsto (fun k => ∑ n ∈ F k, a k n • fseq n t) atTop (𝓝 (f t)) := by
  classical
  let h : ℕ → C(K × realDualUnitBall E, ℝ) :=
    fun n => dualEvaluation (fseq n - u n)
  have hhbound : ∀ n, ‖h n‖ ≤ C + D := by
    intro n
    change ‖dualEvaluation (fseq n - u n)‖ ≤ C + D
    rw [norm_dualEvaluation]
    exact (norm_sub_le _ _).trans (add_le_add (hbound n) (hubound n))
  have hhpoint : ∀ p, Tendsto (fun n => h n p) atTop (𝓝 0) := by
    intro p
    have huφ := ((WeakDual.toStrongDual p.2.val).continuous.tendsto (f p.1)).comp (hu p.1)
    simpa only [h, dualEvaluation_apply, ContinuousMap.sub_apply, map_sub, sub_self]
      using (hweak p.1 (WeakDual.toStrongDual p.2.val)).sub huφ
  have hhweak := continuousMap_uniformlyBounded_pointwiseNull_weak h (C + D) hhbound hhpoint
  choose F a ha hsum htail hsmall using fun k =>
    weakNull_exists_small_convex_tail h hhweak k
      (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
  refine ⟨F, a, ha, hsum, htail, ?_⟩
  intro t
  let g : ℕ → C(K, E) := fun k => ∑ n ∈ F k, a k n • fseq n
  let v : ℕ → C(K, E) := fun k => ∑ n ∈ F k, a k n • u n
  have herror (k : ℕ) : ‖g k - v k‖ < 1 / ((k : ℝ) + 1) := by
    rw [← norm_dualEvaluation]
    have heq : dualEvaluation (g k - v k) = ∑ n ∈ F k, a k n • h n := by
      ext p
      simp only [dualEvaluation_apply, g, v, h, ContinuousMap.sub_apply,
        ContinuousMap.sum_apply, ContinuousMap.smul_apply, map_sub, map_sum, map_smul,
        smul_sub, Finset.sum_sub_distrib]
    rw [heq]
    exact hsmall k
  have hdiff : Tendsto (fun k => g k t - v k t) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact ((g k - v k).norm_coe_le_norm t).trans (herror k).le
  have hv : Tendsto (fun k => v k t) atTop (𝓝 (f t)) := by
    simpa only [v, ContinuousMap.sum_apply, ContinuousMap.smul_apply] using
      finiteConvexTail_tendsto (fun n => u n t) (hu t) F a
        (fun k n hn => ha k n) hsum htail
  have hg := hdiff.add hv
  simpa only [sub_add_cancel, zero_add, g, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply] using hg

end SurveyStatements.P4
