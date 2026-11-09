import SurveyStatements.P1BasicSelection
import SurveyStatements.P1BasicCriterion
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Recursive selection of normalized vectors with one uniform bound for all
initial-sum projections. The accumulating finite dual families ensure that
each earlier norming functional annihilates every later vector.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

private def SelectionState (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] :=
  Finset X × Finset (X →L[ℂ] ℂ)

private theorem selection_exists (hX : ¬ FiniteDimensional ℂ X)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (s : SelectionState X) :
    ∃ v : X, ∃ F : Finset (X →L[ℂ] ℂ),
      ‖v‖ = 1 ∧ v ∉ Submodule.span ℂ (s.1 : Set X) ∧
      (∀ f ∈ s.2, f v = 0) ∧ (∀ f ∈ F, ‖f‖ = 1) ∧
      (∀ x ∈ Submodule.span ℂ (s.1 : Set X), x ≠ 0 →
        ∃ f ∈ F, c * ‖x‖ < ‖f x‖) ∧
      (∀ x ∈ Submodule.span ℂ (s.1 : Set X), ∀ a : ℂ,
        c * ‖x‖ ≤ ‖x + a • v‖) ∧ ∀ f ∈ F, f v = 0 := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (s.1 : Set X)) :=
    FiniteDimensional.span_of_finite ℂ s.1.finite_toSet
  exact finite_basic_selection_step (X := X) hX
    (Submodule.span ℂ (s.1 : Set X)) s.2 hc0 hc1

private def selectionVector (hX : ¬ FiniteDimensional ℂ X)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (s : SelectionState X) : X :=
  Classical.choose (selection_exists hX hc0 hc1 s)

private def selectionFamily (hX : ¬ FiniteDimensional ℂ X)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (s : SelectionState X) :
    Finset (X →L[ℂ] ℂ) :=
  Classical.choose (Classical.choose_spec (selection_exists hX hc0 hc1 s))

private def selectionNext (hX : ¬ FiniteDimensional ℂ X)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (s : SelectionState X) : SelectionState X := by
  classical
  exact (insert (selectionVector hX hc0 hc1 s) s.1,
    s.2 ∪ selectionFamily hX hc0 hc1 s)

private def selectionStates (hX : ¬ FiniteDimensional ℂ X)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : ℕ → SelectionState X
  | 0 => (∅, ∅)
  | n + 1 => selectionNext hX hc0 hc1 (selectionStates hX hc0 hc1 n)

private theorem selection_spec (hX : ¬ FiniteDimensional ℂ X)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (s : SelectionState X) :
    ‖selectionVector hX hc0 hc1 s‖ = 1 ∧
    selectionVector hX hc0 hc1 s ∉ Submodule.span ℂ (s.1 : Set X) ∧
    (∀ f ∈ s.2, f (selectionVector hX hc0 hc1 s) = 0) ∧
    (∀ f ∈ selectionFamily hX hc0 hc1 s, ‖f‖ = 1) ∧
    (∀ x ∈ Submodule.span ℂ (s.1 : Set X), x ≠ 0 →
      ∃ f ∈ selectionFamily hX hc0 hc1 s, c * ‖x‖ < ‖f x‖) ∧
    (∀ x ∈ Submodule.span ℂ (s.1 : Set X), ∀ a : ℂ,
      c * ‖x‖ ≤ ‖x + a • selectionVector hX hc0 hc1 s‖) ∧
    ∀ f ∈ selectionFamily hX hc0 hc1 s, f (selectionVector hX hc0 hc1 s) = 0 :=
  Classical.choose_spec (Classical.choose_spec (selection_exists hX hc0 hc1 s))

/-- Infinite-dimensional normed spaces have normalized linearly independent
sequences whose initial-sum projections admit a common bound.
This is the constructive estimate used in the basic-sequence theorem. -/
theorem exists_uniform_partialSum_sequence (hX : ¬ FiniteDimensional ℂ X)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ e : ℕ → X, (∀ n, ‖e n‖ = 1) ∧
      (∀ n, e n ∉ Submodule.span ℂ (e '' Set.Iio n)) ∧
      ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
        c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖ := by
  classical
  let s := selectionStates hX hc0 hc1
  let e : ℕ → X := fun n => selectionVector hX hc0 hc1 (s n)
  let F : ℕ → Finset (X →L[ℂ] ℂ) := fun n => selectionFamily hX hc0 hc1 (s n)
  have hspec (n : ℕ) := selection_spec hX hc0 hc1 (s n)
  have hnext (n : ℕ) : s (n + 1) = (insert (e n) (s n).1, (s n).2 ∪ F n) := rfl
  have hE : Monotone (fun n => (s n).1) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hnext]
    exact Finset.subset_insert _ _
  have hG : Monotone (fun n => (s n).2) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hnext]
    exact Finset.subset_union_left
  have hprev {i n : ℕ} (hi : i < n) : e i ∈ (s n).1 := by
    apply hE (Nat.succ_le_iff.mpr hi)
    change e i ∈ (s (i + 1)).1
    rw [hnext]
    exact Finset.mem_insert_self _ _
  have hfuture {n m : ℕ} (hnm : n ≤ m) : ∀ f ∈ F n, f (e m) = 0 := by
    intro f hf
    by_cases heq : n = m
    · subst m
      exact (hspec n).2.2.2.2.2.2 f hf
    · have hlt : n < m := lt_of_le_of_ne hnm heq
      apply (hspec m).2.2.1 f
      apply hG (Nat.succ_le_iff.mpr hlt)
      change f ∈ (s (n + 1)).2
      rw [hnext]
      exact Finset.mem_union_right _ hf
  refine ⟨e, fun n => (hspec n).1, ?_, ?_⟩
  · intro n hn
    apply (hspec n).2.1
    apply Submodule.span_mono (show e '' Set.Iio n ⊆ ((s n).1 : Set X) from ?_) hn
    rintro _ ⟨i, hi, rfl⟩
    exact hprev hi
  · intro N M hNM a
    have hp : sequencePartialSum e a N ∈ Submodule.span ℂ ((s N).1 : Set X) := by
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hprev (Finset.mem_range.mp hi)))
    have ht : ∀ f ∈ F N, f (∑ i ∈ Finset.Ico N M, a i • e i) = 0 := by
      intro f hf
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      simp [hfuture (Finset.mem_Ico.mp hi).1 f hf]
    have hb := finite_norming_kernel_bound
      (Submodule.span ℂ ((s N).1 : Set X)) hc0 (F N)
      (hspec N).2.2.2.1 (hspec N).2.2.2.2.1 hp ht
    simpa only [sequencePartialSum, Finset.sum_range_add_sum_Ico _ hNM] using hb

/-- A normalized basic sequence exists in every infinite-dimensional complex
normed space, with any chosen uniform basis bound larger than one. -/
theorem exists_normalized_basicSequence_with_bound
    (hX : ¬ FiniteDimensional ℂ X) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ e : ℕ → X, (∀ n, ‖e n‖ = 1) ∧ IsBasicSequence e ∧
      ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
        c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖ := by
  obtain ⟨e, he, _, hb⟩ := exists_uniform_partialSum_sequence hX hc0 hc1
  exact ⟨e, he, basicSequence_of_uniform_partialSum he hc0 hb, hb⟩

theorem exists_normalized_basicSequence (hX : ¬ FiniteDimensional ℂ X) :
    ∃ e : ℕ → X, (∀ n, ‖e n‖ = 1) ∧ IsBasicSequence e := by
  obtain ⟨e, he, hbasic, _⟩ := exists_normalized_basicSequence_with_bound
    hX (c := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  exact ⟨e, he, hbasic⟩

private def varyingSelectionStates (hX : ¬ FiniteDimensional ℂ X)
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 < c n) (hc1 : ∀ n, c n < 1) : ℕ → SelectionState X
  | 0 => (∅, ∅)
  | n + 1 => selectionNext hX (hc0 n) (hc1 n) (varyingSelectionStates hX c hc0 hc1 n)

/-- Stage-dependent norming families control every finite initial interval. -/
theorem exists_varying_partialSum_sequence (hX : ¬ FiniteDimensional ℂ X)
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 < c n) (hc1 : ∀ n, c n < 1) :
    ∃ e : ℕ → X, (∀ n, ‖e n‖ = 1) ∧
      (∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
        c N * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖) ∧
      ∀ p q r : ℕ, p ≤ q → q ≤ r → ∀ a : ℕ → ℂ,
        c (q + 1) * ‖∑ i ∈ Finset.Icc p q, a i • e i‖ ≤
          ‖∑ i ∈ Finset.Icc p r, a i • e i‖ := by
  classical
  let s := varyingSelectionStates hX c hc0 hc1
  let e : ℕ → X := fun n => selectionVector hX (hc0 n) (hc1 n) (s n)
  let F : ℕ → Finset (X →L[ℂ] ℂ) :=
    fun n => selectionFamily hX (hc0 n) (hc1 n) (s n)
  have hspec n := selection_spec hX (hc0 n) (hc1 n) (s n)
  have hnext (n : ℕ) : s (n + 1) = (insert (e n) (s n).1, (s n).2 ∪ F n) := rfl
  have hE : Monotone (fun n => (s n).1) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hnext]
    exact Finset.subset_insert _ _
  have hG : Monotone (fun n => (s n).2) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hnext]
    exact Finset.subset_union_left
  have hprev {i n : ℕ} (hi : i < n) : e i ∈ (s n).1 := by
    apply hE (Nat.succ_le_iff.mpr hi)
    change e i ∈ (s (i + 1)).1
    rw [hnext]
    exact Finset.mem_insert_self _ _
  have hfuture {n m : ℕ} (hnm : n ≤ m) : ∀ f ∈ F n, f (e m) = 0 := by
    intro f hf
    by_cases heq : n = m
    · subst m
      exact (hspec n).2.2.2.2.2.2 f hf
    · have hlt : n < m := lt_of_le_of_ne hnm heq
      apply (hspec m).2.2.1 f
      apply hG (Nat.succ_le_iff.mpr hlt)
      change f ∈ (s (n + 1)).2
      rw [hnext]
      exact Finset.mem_union_right _ hf
  refine ⟨e, fun n => (hspec n).1, ?_, ?_⟩
  · intro N M hNM a
    have hp : sequencePartialSum e a N ∈ Submodule.span ℂ ((s N).1 : Set X) := by
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hprev (Finset.mem_range.mp hi)))
    have ht : ∀ f ∈ F N, f (∑ i ∈ Finset.Ico N M, a i • e i) = 0 := by
      intro f hf
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      simp [hfuture (Finset.mem_Ico.mp hi).1 f hf]
    have hb := finite_norming_kernel_bound
      (Submodule.span ℂ ((s N).1 : Set X)) (hc0 N) (F N)
      (hspec N).2.2.2.1 (hspec N).2.2.2.2.1 hp ht
    simpa only [sequencePartialSum, Finset.sum_range_add_sum_Ico _ hNM] using hb
  · intro p q r hpq hqr a
    have hp : (∑ i ∈ Finset.Icc p q, a i • e i) ∈
        Submodule.span ℂ ((s (q + 1)).1 : Set X) := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      have hi' := Finset.mem_Icc.mp hi
      exact Submodule.subset_span (hprev (by omega))
    have ht : ∀ f ∈ F (q + 1), f (∑ i ∈ Finset.Ioc q r, a i • e i) = 0 := by
      intro f hf
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_Ioc.mp hi
      simp [hfuture (by omega : q + 1 ≤ i) f hf]
    have hdis : Disjoint (Finset.Icc p q) (Finset.Ioc q r) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have := Finset.mem_Icc.mp hi
      have := Finset.mem_Ioc.mp hj
      omega
    have hunion : Finset.Icc p q ∪ Finset.Ioc q r = Finset.Icc p r := by
      ext i
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hb := finite_norming_kernel_bound
      (Submodule.span ℂ ((s (q + 1)).1 : Set X)) (hc0 (q + 1)) (F (q + 1))
      (hspec (q + 1)).2.2.2.1 (hspec (q + 1)).2.2.2.2.1 hp ht
    rwa [← Finset.sum_union hdis, hunion] at hb

/-- Every infinite-dimensional complex normed space has a normalized
asymptotically monotone basic sequence. -/
theorem exists_asymptoticallyMonotone_with_bound (hX : ¬ FiniteDimensional ℂ X) :
    ∃ e : ℕ → X, IsAsymptoticallyMonotone e ∧
      ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
        (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖ := by
  let c : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ (n + 1)
  have hcge (n : ℕ) : 1 / 2 ≤ c n := by
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [c]
    rw [pow_succ]
    nlinarith
  have hc0 (n : ℕ) : 0 < c n := by linarith [hcge n]
  have hc1 (n : ℕ) : c n < 1 := by
    dsimp [c]
    have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
    linarith
  have hc : Tendsto c atTop (𝓝 (1 : ℝ)) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [c] using tendsto_const_nhds.sub (hp.comp (tendsto_add_atTop_nat 1))
  obtain ⟨e, he, hb, hi⟩ := exists_varying_partialSum_sequence hX c hc0 hc1
  have hhalf : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖ := by
    intro N M hNM a
    exact (mul_le_mul_of_nonneg_right (hcge N) (norm_nonneg _)).trans (hb N M hNM a)
  refine ⟨e, ⟨basicSequence_of_uniform_partialSum he (by norm_num) hhalf, he, ?_⟩, hhalf⟩
  intro γ hγ
  have hthreshold : 1 / (1 + γ) < (1 : ℝ) := by
    apply (div_lt_one (by linarith)).mpr
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hc.eventually (eventually_gt_nhds hthreshold))
  refine ⟨N, ?_⟩
  intro p q r hNp hpq hqr a
  have hcn := hN (q + 1) (by omega)
  have hprod : 1 ≤ (1 + γ) * c (q + 1) := by
    have hpos : 0 < 1 + γ := by linarith
    simpa [mul_comm] using (div_le_iff₀ hpos).mp hcn.le
  have hproj := hi p q r hpq hqr a
  nlinarith [norm_nonneg (∑ i ∈ Finset.Icc p q, a i • e i)]

/-- The direct selection theorem with no prescribed uniform basis bound. -/
theorem exists_asymptoticallyMonotone (hX : ¬ FiniteDimensional ℂ X) :
    ∃ e : ℕ → X, IsAsymptoticallyMonotone e := by
  obtain ⟨e, he, _⟩ := exists_asymptoticallyMonotone_with_bound hX
  exact ⟨e, he⟩

end SurveyStatements.P1

