import PL1.SchurBoundedCompleteness

/-! # Weak sequential completeness with the entire continuous dual

The generic Schur argument is reused from `SchurBoundedCompleteness`.
A weak Cauchy sequence in a complete Schur space has an actual norm limit,
and therefore a weak limit against every continuous linear functional.
-/

noncomputable section
open Filter
open scoped Topology
namespace PL1

variable {K E F : Type*} [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

/-- Every member of the full continuous dual sends the sequence to a Cauchy sequence. -/
abbrev WeaklyCauchy (K E : Type*) [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]
    (x : ℕ → E) : Prop := SchurBoundedCompleteness.WeaklyCauchy (𝕜 := K) x

/-- Weak sequential completeness uses the original continuous dual and original space. -/
def IsWeaklySequentiallyComplete (K E : Type*) [RCLike K]
    [NormedAddCommGroup E] [NormedSpace K E] : Prop :=
  ∀ x : ℕ → E, WeaklyCauchy K E x → ∃ a : E, WeaklyConverges K E x a

theorem WeaklyCauchy.map {x : ℕ → E} (hx : WeaklyCauchy K E x) (T : E →L[K] F) :
    WeaklyCauchy K F (fun n => T (x n)) := fun φ => hx (φ.comp T)

/-- Completeness of the space is unnecessary for the norm Cauchy conclusion. -/
theorem HasSchurProperty.cauchySeq_of_weaklyCauchy (hS : HasSchurProperty K E)
    {x : ℕ → E} (hx : WeaklyCauchy K E x) : CauchySeq x :=
  SchurBoundedCompleteness.cauchySeq_of_weaklyCauchy hS hx

/-- A weak Cauchy sequence in a complete Schur space converges in its original norm. -/
theorem HasSchurProperty.exists_norm_limit_of_weaklyCauchy [CompleteSpace E]
    (hS : HasSchurProperty K E) {x : ℕ → E} (hx : WeaklyCauchy K E x) :
    ∃ a : E, Tendsto x atTop (𝓝 a) :=
  SchurBoundedCompleteness.exists_tendsto_of_weaklyCauchy hS hx

/-- Every complete Schur space is weakly sequentially complete. -/
theorem HasSchurProperty.isWeaklySequentiallyComplete [CompleteSpace E]
    (hS : HasSchurProperty K E) : IsWeaklySequentiallyComplete K E := by
  intro x hx
  obtain ⟨a, ha⟩ := hS.exists_norm_limit_of_weaklyCauchy hx
  exact ⟨a, weaklyConverges_of_tendsto ha⟩

/-- Failure of norm Cauchy convergence in a Schur space is witnessed by a genuine dual functional. -/
theorem HasSchurProperty.exists_dual_not_cauchy (hS : HasSchurProperty K E)
    {x : ℕ → E} (hx : ¬ CauchySeq x) : ∃ φ : E →L[K] K, ¬ CauchySeq (fun n => φ (x n)) := by
  by_contra h
  push Not at h
  exact hx (hS.cauchySeq_of_weaklyCauchy h)

/-- The same dual witness oscillates by a fixed positive amount arbitrarily far out. -/
theorem HasSchurProperty.exists_dual_oscillation (hS : HasSchurProperty K E)
    {x : ℕ → E} (hx : ¬ CauchySeq x) :
    ∃ (φ : E →L[K] K) (ε : ℝ), 0 < ε ∧
      ∀ N : ℕ, ∃ m ≥ N, ∃ n ≥ N, ε ≤ ‖φ (x m) - φ (x n)‖ := by
  obtain ⟨φ, hφ⟩ := hS.exists_dual_not_cauchy hx
  rw [Metric.cauchySeq_iff] at hφ
  push Not at hφ
  simpa only [dist_eq_norm] using (show ∃ (φ : E →L[K] K) (ε : ℝ), 0 < ε ∧
    ∀ N : ℕ, ∃ m ≥ N, ∃ n ≥ N, ε ≤ dist (φ (x m)) (φ (x n)) from ⟨φ, hφ⟩)

#print axioms HasSchurProperty.isWeaklySequentiallyComplete
#print axioms HasSchurProperty.exists_dual_oscillation
end PL1
