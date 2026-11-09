import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Genuine finite convex tail selection from weak convergence. -/

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Membership in the convex hull of a sequence tail has ordinary finite
coefficients indexed by the original natural numbers. Repeated indices are
combined by summing their weights. -/
theorem convexHull_tail_coefficients (f : ℕ → E) (k : ℕ) {v : E}
    (hv : v ∈ convexHull ℝ (f '' Set.Ici k)) :
    ∃ (F : Finset ℕ) (a : ℕ → ℝ),
      (∀ n, 0 ≤ a n) ∧ (∑ n ∈ F, a n = 1) ∧
      (∀ n ∈ F, k ≤ n) ∧ ∑ n ∈ F, a n • f n = v := by
  classical
  obtain ⟨I, hI, w, z, hw, hsum, hz, heq⟩ :=
    mem_convexHull_iff_exists_fintype.mp hv
  letI : Fintype I := hI
  choose n hn hzn using hz
  let F : Finset ℕ := Finset.univ.image n
  let a : ℕ → ℝ := fun m => ∑ i ∈ Finset.univ with n i = m, w i
  have ha : ∀ m, 0 ≤ a m := fun m =>
    Finset.sum_nonneg (fun i hi => hw i)
  have hweights : ∑ m ∈ F, a m = ∑ i, w i := by
    exact Finset.sum_image' (s := Finset.univ) (g := n) (h := w) (fun i hi => rfl)
  have hvectors : ∑ m ∈ F, a m • f m = ∑ i, w i • f (n i) := by
    apply Finset.sum_image' (s := Finset.univ) (g := n) (h := fun i => w i • f (n i))
    intro i hi
    dsimp [a]
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  refine ⟨F, a, ha, hweights.trans hsum, ?_, ?_⟩
  · intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    exact hn i
  · rw [hvectors]
    simpa only [hzn] using heq

/-- Mazur's argument on each tail: a weakly null sequence has finite convex
combinations of any prescribed tail with arbitrarily small norm. -/
theorem weakNull_exists_small_convex_tail (f : ℕ → E)
    (hf : Tendsto (fun n => toWeakSpace ℝ E (f n)) atTop (𝓝 0))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset ℕ) (a : ℕ → ℝ),
      (∀ n, 0 ≤ a n) ∧ (∑ n ∈ F, a n = 1) ∧
      (∀ n ∈ F, k ≤ n) ∧ ‖∑ n ∈ F, a n • f n‖ < ε := by
  classical
  let H := convexHull ℝ (f '' Set.Ici k)
  have hweak : (0 : WeakSpace ℝ E) ∈ closure (toWeakSpace ℝ E '' H) := by
    apply mem_closure_of_tendsto hf
    filter_upwards [eventually_ge_atTop k] with n hn
    exact ⟨f n, subset_convexHull ℝ _ ⟨n, hn, rfl⟩, rfl⟩
  have hzero : (0 : E) ∈ closure H := by
    rw [← (convex_convexHull ℝ (f '' Set.Ici k)).toWeakSpace_closure ℝ] at hweak
    obtain ⟨v, hv, heq⟩ := hweak
    have hv0 : v = 0 := (toWeakSpace ℝ E).injective (by simpa using heq)
    simpa only [hv0] using hv
  obtain ⟨v, hv, hnear⟩ := Metric.mem_closure_iff.mp hzero ε hε
  obtain ⟨F, a, ha, hsum, htail, heq⟩ := convexHull_tail_coefficients f k hv
  refine ⟨F, a, ha, hsum, htail, ?_⟩
  rw [heq]
  simpa only [dist_zero_left] using hnear

end SurveyStatements.P4
