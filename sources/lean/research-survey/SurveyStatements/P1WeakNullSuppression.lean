import SurveyStatements.P1SuppressionAssignmentContradiction
import SurveyStatements.P1SuppressionRestriction
import SurveyStatements.P1PreferredSupportSelection
import SurveyStatements.P1WeakNullSelection

/-! Unit-modulus suppression selected from an actual normalized weakly null
sequence, and the resulting toroidal separation. Every selector input is
constructed from a concrete failure witness; no structural dichotomy or
separation conclusion is assumed. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped BigOperators Classical

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem weakNull_exists_unitModulusSuppressionOn
    (e : ℕ → X) (he : ∀ n, ‖e n‖ = 1)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (hweak : ∀ f : StrongDual ℂ X, Tendsto (fun i => f (e i)) atTop (𝓝 0)) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : Set ℕ, N.Infinite ∧ HasUnitModulusSuppressionOn e K N := by
  classical
  by_contra hno
  obtain ⟨A, _, hA, D, hD, hsector⟩ := exists_complex_phase_sector_witness
  have hK : 0 < (120 : ℝ) * D := by positivity
  have hfail (M : Set ℕ) (hM : M.Infinite) :
      ¬ HasUnitModulusSuppressionOn e (120 * D) M := by
    intro h
    exact hno ⟨120 * D, hK, M, hM, h⟩
  have hex (M : Set ℕ) (hM : M.Infinite) :
      ∃ w : UnitSuppressionWitness e A, (w.coefficients.support : Set ℕ) ⊆ M :=
    exists_unitSuppressionWitness_of_failure e he hp A D hD hsector M (hfail M hM)
  obtain ⟨φ, hvalid, hlocal, hmutual, hthin⟩ := exists_preferred_support_selection
    (fun w : UnitSuppressionWitness e A => w.coefficients.support)
    (fun w => w.selected_nonempty.mono w.selected_subset) hex
  have hsame (P Q : Set ℕ) (hP : P.Infinite) (hQ : Q.Infinite)
      (hs : (φ P).coefficients.support = (φ Q).coefficients.support) : φ P = φ Q := by
    apply (hmutual P Q hP hQ ?_ ?_).symm
    · rw [← hs]
      exact hvalid P hP
    · rw [hs]
      exact hvalid Q hQ
  exact unitSuppressionWitness_assignment_contradiction e he hp hweak A hA φ
    hvalid hlocal hsame hthin

theorem normalized_weakNull_toroidal_elton_odell [CompleteSpace X]
    (y : ℕ → X) (hynorm : ∀ n, ‖y n‖ = 1)
    (hy : ∀ f : StrongDual ℂ X, Tendsto (fun n => f (y n)) atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  obtain ⟨ν, hν, ham, hprefix⟩ :=
    weakNull_exists_asymptoticallyMonotone_subsequence_with_bound y hynorm hy
  let e := y ∘ ν
  have he (n : ℕ) : ‖e n‖ = 1 := hynorm (ν n)
  have heweak (f : StrongDual ℂ X) : Tendsto (fun n => f (e n)) atTop (𝓝 0) :=
    (hy f).comp hν.tendsto_atTop
  obtain ⟨K, hK, N, hN, hsupp⟩ := weakNull_exists_unitModulusSuppressionOn e he hprefix heweak
  obtain ⟨η, hη, hηN⟩ := infiniteSet_exists_strictMono_sequence N hN
  have hηsupp := hsupp.subsequence η hη.injective hηN
  have hηnorm (n : ℕ) : ‖(e ∘ η) n‖ = 1 := he (η n)
  have hηweak (f : StrongDual ℂ X) : Tendsto (fun n => f ((e ∘ η) n)) atTop (𝓝 0) :=
    (heweak f).comp hη.tendsto_atTop
  obtain ⟨μ, hμ, ham', hprefix'⟩ :=
    weakNull_exists_asymptoticallyMonotone_subsequence_with_bound (e ∘ η) hηnorm hηweak
  exact unitModulusSuppression_toroidal_elton_odell ((e ∘ η) ∘ μ) ham' hprefix'
    hK.le (hηsupp.subsequence μ hμ.injective)

end SurveyStatements.P1
