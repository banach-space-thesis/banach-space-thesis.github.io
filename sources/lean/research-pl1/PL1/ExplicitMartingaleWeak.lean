import PL1.ExplicitMartingale
import PL1.SchurExample
import PL1.WeakSequentialCompleteness
import PL1.RealSchur

/-! # Every explicit increasing-rate martingale trajectory fails to be weakly Cauchy

The conclusion quantifies over the entire continuous dual of the actual
intrinsic Banach space. In particular no countable set of weak tests replaces it.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace PL1.ExplicitMartingale
open Noise Walsh

variable (K : Type*) [RCLike K]

/-- The actual increasing-rate intrinsic space is weakly sequentially complete. -/
theorem schur_intrinsic_weaklySequentiallyComplete :
    IsWeaklySequentiallyComplete K (dyadicSystem K schurRates).IntrinsicSpace :=
  (schurRates_intrinsic_hasSchurProperty K).isWeaklySequentiallyComplete

/-- Every trajectory of the explicit martingale fails the full-dual weak Cauchy test. -/
theorem schur_beta_not_weaklyCauchy (s : Walsh.Group) :
    ¬ WeaklyCauchy K (dyadicSystem K schurRates).IntrinsicSpace
      (fun m => beta K schurRates m s) := by
  intro h
  exact schur_beta_not_cauchy K s
    ((schurRates_intrinsic_hasSchurProperty K).cauchySeq_of_weaklyCauchy h)

/-- Each trajectory has an actual continuous linear functional witnessing scalar non-Cauchyness. -/
theorem schur_beta_exists_dual_not_cauchy (s : Walsh.Group) :
    ∃ φ : (dyadicSystem K schurRates).IntrinsicSpace →L[K] K,
      ¬ CauchySeq (fun m => φ (beta K schurRates m s)) :=
  (schurRates_intrinsic_hasSchurProperty K).exists_dual_not_cauchy (schur_beta_not_cauchy K s)

/-- A fixed positive scalar oscillation persists arbitrarily far along every trajectory. -/
theorem schur_beta_exists_dual_oscillation (s : Walsh.Group) :
    ∃ (φ : (dyadicSystem K schurRates).IntrinsicSpace →L[K] K) (ε : ℝ), 0 < ε ∧
      ∀ N : ℕ, ∃ m ≥ N, ∃ n ≥ N,
        ε ≤ ‖φ (beta K schurRates m s) - φ (beta K schurRates n s)‖ :=
  (schurRates_intrinsic_hasSchurProperty K).exists_dual_oscillation (schur_beta_not_cauchy K s)

/-- The distinguished explicit sequence also fails to be weakly Cauchy. -/
theorem schur_sequence_not_weaklyCauchy :
    ¬ WeaklyCauchy K (dyadicSystem K schurRates).IntrinsicSpace (sequence K schurRates) :=
  schur_beta_not_weaklyCauchy K 1

/-- The same conclusion holds for the real continuous dual of either scalar-field construction. -/
theorem schur_beta_not_weaklyCauchy_real (s : Walsh.Group) :
    ¬ WeaklyCauchy ℝ (dyadicSystem K schurRates).IntrinsicSpace
      (fun m => beta K schurRates m s) := by
  have hS : HasSchurProperty ℝ (dyadicSystem K schurRates).IntrinsicSpace :=
    hasSchurProperty_iff_real.mp (schurRates_intrinsic_hasSchurProperty K)
  exact fun h => schur_beta_not_cauchy K s (hS.cauchySeq_of_weaklyCauchy h)

#print axioms schur_intrinsic_weaklySequentiallyComplete
#print axioms schur_beta_not_weaklyCauchy
#print axioms schur_beta_exists_dual_oscillation
#print axioms schur_beta_not_weaklyCauchy_real
end PL1.ExplicitMartingale
