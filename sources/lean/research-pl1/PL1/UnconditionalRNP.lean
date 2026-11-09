import PL1.DecompositionRNP
import PL1.UnconditionalDecomposition

/-! # Schur spaces with unconditional finite-dimensional projections have RNP

This proves the analytic implication once the actual finite-dimensional
projections are supplied. It makes no assertion that an arbitrary Banach
lattice has a basis or a sequence of such projections.
-/

noncomputable section
universe u v
open Filter
open scoped Topology BigOperators

namespace PL1.UnconditionalRNP

open DecompositionRNP UnconditionalDecomposition

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The projection differences telescope on every vector. -/
theorem sum_difference_apply (P : ℕ → E →L[ℝ] E) (N : ℕ) (y : E) :
    (∑ j ∈ Finset.range (N + 1), difference P j y) = P N y := by
  have h : ∀ j, difference P j y = branchDifference (fun n => P n y) j := by
    intro j
    cases j <;> rfl
  simpa only [h] using sum_branchDifference (fun n => P n y) N

/-- The all-positive choice of signs bounds the partial-sum projections. -/
theorem norm_projection_le_of_sign_bound
    (P : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (htransform : ∀ (N : ℕ) (ε : ℕ → ℝ) (y : E),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), ε j • difference P j y‖ ≤ C * ‖y‖)
    (N : ℕ) : ‖P N‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro y
  have h := htransform N (fun _ => 1) y (fun _ => Or.inl rfl)
  simpa only [one_smul, sum_difference_apply] using h

/-- The full vector-measure RNP follows from the Schur property and an actual
unconditional finite-dimensional projection decomposition. -/
theorem hasRadonNikodymProperty_of_schur_unconditional_projections [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (P : ℕ → E →L[ℝ] E)
    (hfinite : ∀ n, FiniteDimensional ℝ (P n).range)
    (hnested : ∀ m n, m ≤ n → (P m).comp (P n) = P m)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (C : ℝ) (hC : 0 ≤ C)
    (htransform : ∀ (N : ℕ) (ε : ℕ → ℝ) (y : E),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), ε j • difference P j y‖ ≤ C * ‖y‖) :
    HasRadonNikodymProperty.{u, v} E := by
  apply hasRadonNikodymProperty_of_boundedlyCompleteDecomposition
  exact {
    projection := P
    finiteDimensional := hfinite
    nested := hnested
    uniformBound := ⟨C, norm_projection_le_of_sign_bound P C hC htransform⟩
    tendsto_identity := hstrong
    bounded_complete := bounded_branch_converges hS P C hC htransform }

/-- A Schur space failing RNP cannot have uniformly bounded sign transforms
for any strongly convergent nested finite-dimensional projection decomposition. -/
theorem no_uniform_sign_bound_of_not_RNP [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (hRNP : ¬ HasRadonNikodymProperty.{u, v} E)
    (P : ℕ → E →L[ℝ] E)
    (hfinite : ∀ n, FiniteDimensional ℝ (P n).range)
    (hnested : ∀ m n, m ≤ n → (P m).comp (P n) = P m)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ε : ℕ → ℝ) (y : E),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), ε j • difference P j y‖ ≤ C * ‖y‖ := by
  rintro ⟨C, hC, htransform⟩
  exact hRNP (hasRadonNikodymProperty_of_schur_unconditional_projections
    hS P hfinite hnested hstrong C hC htransform)

end PL1.UnconditionalRNP
