import SurveyStatements.P1KernelPrefixBound
import SurveyStatements.P1WeakNullSelectionStep
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-! Basic subsequence selection for a normalized sequence annihilated in
the limit by an isomorphically norming kernel of the dual. All chosen
functionals remain in that kernel throughout the finite-family recursion. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped BigOperators
open scoped Classical

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

private abbrev KernelSelectionState (ξ : StrongDual ℂ (StrongDual ℂ X)) :=
  Finset X × {G : Finset (StrongDual ℂ X) // ∀ f ∈ G, ξ f = 0} × ℕ

private def kernelSelectionFamily
    (ξ : StrongDual ℂ (StrongDual ℂ X)) {q d : ℝ}
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖)
    (hd : d < q) (s : KernelSelectionState ξ) : Finset (StrongDual ℂ X) := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (s.1 : Set X)) :=
    FiniteDimensional.span_of_finite ℂ s.1.finite_toSet
  exact Classical.choose (finite_kernel_norming_family ξ hq hd
    (Submodule.span ℂ (s.1 : Set X)))

private theorem kernelSelectionFamily_spec
    (ξ : StrongDual ℂ (StrongDual ℂ X)) {q d : ℝ}
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖)
    (hd : d < q) (s : KernelSelectionState ξ) :
    (∀ f ∈ kernelSelectionFamily ξ hq hd s, ‖f‖ ≤ 1 ∧ ξ f = 0) ∧
      ∀ x ∈ Submodule.span ℂ (s.1 : Set X), x ≠ 0 →
        ∃ f ∈ kernelSelectionFamily ξ hq hd s, d * ‖x‖ < ‖f x‖ := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (s.1 : Set X)) :=
    FiniteDimensional.span_of_finite ℂ s.1.finite_toSet
  exact Classical.choose_spec (finite_kernel_norming_family ξ hq hd
    (Submodule.span ℂ (s.1 : Set X)))

private theorem kernelSelectionIndex_exists
    (y : ℕ → X) (ξ : StrongDual ℂ (StrongDual ℂ X))
    (hy : ∀ f : StrongDual ℂ X, ξ f = 0 →
      Tendsto (fun n => f (y n)) atTop (𝓝 0)) {q d : ℝ}
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖)
    (hd : d < q) (s : KernelSelectionState ξ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, s.2.2 ≤ n ∧
      ∀ f ∈ s.2.1.val ∪ kernelSelectionFamily ξ hq hd s, ‖f (y n)‖ < δ := by
  classical
  have hsmall : ∀ᶠ n in atTop,
      ∀ f ∈ s.2.1.val ∪ kernelSelectionFamily ξ hq hd s, ‖f (y n)‖ < δ := by
    rw [eventually_all_finset]
    intro f hf
    have hfker : ξ f = 0 := by
      rcases Finset.mem_union.mp hf with hf | hf
      · exact s.2.1.property f hf
      · exact ((kernelSelectionFamily_spec ξ hq hd s).1 f hf).2
    have ht : Tendsto (fun n => ‖f (y n)‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using (hy f hfker).norm
    exact ht.eventually (eventually_lt_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  exact ⟨max s.2.2 N, Nat.le_max_left _ _, hN _ (Nat.le_max_right _ _)⟩

private def kernelSelectionIndex
    (y : ℕ → X) (ξ : StrongDual ℂ (StrongDual ℂ X))
    (hy : ∀ f : StrongDual ℂ X, ξ f = 0 →
      Tendsto (fun n => f (y n)) atTop (𝓝 0)) {q d : ℝ}
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖)
    (hd : d < q) (s : KernelSelectionState ξ) {δ : ℝ} (hδ : 0 < δ) : ℕ :=
  Classical.choose (kernelSelectionIndex_exists y ξ hy hq hd s hδ)

private def kernelSelectionNext
    (y : ℕ → X) (ξ : StrongDual ℂ (StrongDual ℂ X))
    (hy : ∀ f : StrongDual ℂ X, ξ f = 0 →
      Tendsto (fun n => f (y n)) atTop (𝓝 0)) {q d : ℝ}
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖)
    (hd : d < q) (s : KernelSelectionState ξ) {δ : ℝ} (hδ : 0 < δ) :
    KernelSelectionState ξ := by
  classical
  let n := kernelSelectionIndex y ξ hy hq hd s hδ
  refine (insert (y n) s.1, ⟨s.2.1.val ∪ kernelSelectionFamily ξ hq hd s, ?_⟩, n + 1)
  intro f hf
  rcases Finset.mem_union.mp hf with hf | hf
  · exact s.2.1.property f hf
  · exact ((kernelSelectionFamily_spec ξ hq hd s).1 f hf).2

private def kernelSelectionStates
    (y : ℕ → X) (ξ : StrongDual ℂ (StrongDual ℂ X))
    (hy : ∀ f : StrongDual ℂ X, ξ f = 0 →
      Tendsto (fun n => f (y n)) atTop (𝓝 0)) {q d : ℝ}
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖)
    (hd : d < q) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ℕ → KernelSelectionState ξ
  | 0 => (∅, ⟨∅, by simp⟩, 0)
  | n + 1 => kernelSelectionNext y ξ hy hq hd
      (kernelSelectionStates y ξ hy hq hd ε hε n) (hε n)

theorem exists_kernel_small_evaluation_subsequence
    (y : ℕ → X) (ξ : StrongDual ℂ (StrongDual ℂ X))
    (hy : ∀ f : StrongDual ℂ X, ξ f = 0 →
      Tendsto (fun n => f (y n)) atTop (𝓝 0)) {q d : ℝ}
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖)
    (hd : d < q) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∃ F : ℕ → Finset (StrongDual ℂ X),
      (∀ N f, f ∈ F N → ‖f‖ ≤ 1 ∧ ξ f = 0) ∧
      (∀ N, ∀ x ∈ Submodule.span ℂ ((y ∘ ν) '' (Finset.range N : Set ℕ)),
        x ≠ 0 → ∃ f ∈ F N, d * ‖x‖ < ‖f x‖) ∧
      ∀ N i, N ≤ i → ∀ f ∈ F N, ‖f ((y ∘ ν) i)‖ ≤ ε i := by
  classical
  let s := kernelSelectionStates y ξ hy hq hd ε hε
  let ν : ℕ → ℕ := fun n => kernelSelectionIndex y ξ hy hq hd (s n) (hε n)
  let F : ℕ → Finset (StrongDual ℂ X) := fun n => kernelSelectionFamily ξ hq hd (s n)
  have hspec (n : ℕ) : (s n).2.2 ≤ ν n ∧
      ∀ f ∈ (s n).2.1.val ∪ F n, ‖f (y (ν n))‖ < ε n :=
    Classical.choose_spec (kernelSelectionIndex_exists y ξ hy hq hd (s n) (hε n))
  have hnextV (n : ℕ) : (s (n + 1)).1 = insert (y (ν n)) (s n).1 := rfl
  have hnextG (n : ℕ) : (s (n + 1)).2.1.val = (s n).2.1.val ∪ F n := rfl
  have hnextL (n : ℕ) : (s (n + 1)).2.2 = ν n + 1 := rfl
  have hν : StrictMono ν := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hn := (hspec (n + 1)).1
    rw [hnextL] at hn
    exact Nat.lt_of_succ_le hn
  have hmonoV : Monotone (fun n => (s n).1) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hnextV]
    exact Finset.subset_insert _ _
  have hmonoG : Monotone (fun n => (s n).2.1.val) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hnextG]
    exact Finset.subset_union_left
  refine ⟨ν, hν, F, ?_, ?_, ?_⟩
  · intro N f hf
    exact (kernelSelectionFamily_spec ξ hq hd (s N)).1 f hf
  · intro N x hx hx0
    apply (kernelSelectionFamily_spec ξ hq hd (s N)).2 x _ hx0
    apply Submodule.span_mono _ hx
    rintro _ ⟨i, hi, rfl⟩
    have hiN : i < N := Finset.mem_range.mp hi
    apply hmonoV (Nat.succ_le_of_lt hiN)
    change y (ν i) ∈ (s (i + 1)).1
    rw [hnextV]
    exact Finset.mem_insert_self _ _
  · intro N i hNi f hf
    apply ((hspec i).2 f _).le
    by_cases hEq : N = i
    · subst N
      exact Finset.mem_union_right _ hf
    · apply Finset.mem_union_left
      apply hmonoG (show N + 1 ≤ i by omega)
      change f ∈ (s (N + 1)).2.1.val
      rw [hnextG]
      exact Finset.mem_union_right _ hf

theorem normalized_kernelNull_exists_basic_subsequence
    (y : ℕ → X) (hynorm : ∀ n, ‖y n‖ = 1)
    (ξ : StrongDual ℂ (StrongDual ℂ X))
    (hy : ∀ f : StrongDual ℂ X, ξ f = 0 →
      Tendsto (fun n => f (y n)) atTop (𝓝 0)) {q : ℝ} (hqpos : 0 < q)
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ IsBasicSequence (y ∘ ν) ∧
      ∀ N M, N ≤ M → ∀ a : ℕ → ℂ,
        (q / 4) * ‖sequencePartialSum (y ∘ ν) a N‖ ≤
          ‖sequencePartialSum (y ∘ ν) a M‖ := by
  let d : ℝ := q / 2
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hdq : d < q := by dsimp [d]; linarith
  let ε : ℕ → ℝ := fun n => (d / 8) * (1 / 2 : ℝ) ^ n
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hbudget (M : ℕ) : ∑ i ∈ Finset.range M, ε i ≤ d / 4 := by
    dsimp only [ε]
    rw [← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le M)
      (show 0 ≤ d / 8 by positivity)
    convert h using 1 <;> ring
  obtain ⟨ν, hν, F, hF, hnorm, hfuture⟩ :=
    exists_kernel_small_evaluation_subsequence y ξ hy hq hdq ε hεpos
  have hbound := kernel_norming_uniform_prefix_bound (y ∘ ν)
    (fun n => hynorm (ν n)) F hdpos
    (fun N f hf => (hF N f hf).1) hnorm ε
    (fun n => (hεpos n).le) hbudget hfuture
  have hbound' : ∀ N M, N ≤ M → ∀ a : ℕ → ℂ,
      (q / 4) * ‖sequencePartialSum (y ∘ ν) a N‖ ≤
        ‖sequencePartialSum (y ∘ ν) a M‖ := by
    convert hbound using 1 <;> dsimp [d] <;> ring
  exact ⟨ν, hν, basicSequence_of_uniform_partialSum (fun n => hynorm (ν n))
    (by positivity) hbound', hbound'⟩

end SurveyStatements.P1
