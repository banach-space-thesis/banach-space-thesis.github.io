import SurveyStatements.P1AlmostIsometric
import SurveyStatements.P1Completion
import SurveyStatements.P1ClassicalSequences
import SurveyStatements.P1C0Sequence
import SurveyStatements.P1BasicSequences
import SurveyStatements.P1BasicConstruction
import SurveyStatements.P1RapidEstimates
import SurveyStatements.P1WeakDifferences
import SurveyStatements.P1RapidCompactness
import SurveyStatements.P1FiniteNets
import SurveyStatements.P1ReflexiveSeparation
import SurveyStatements.P1StronglySummingSeparation
import SurveyStatements.P1L1Embedding
import SurveyStatements.P1C0Embedding
import SurveyStatements.P1NonreflexiveSequence
import SurveyStatements.P1ComplexRosenthal
import SurveyStatements.P1WeakCauchySuppressionSeparation

/-!
# Problem 1: toroidal Elton–Odell

Source: `source/problems/P1-toroidal-elton-odell.tex`,
Theorem `p1-first:thm:main`.
Completeness is deliberately not assumed: the source concerns normed spaces.
-/

noncomputable section

set_option autoImplicit false

universe u

namespace SurveyStatements.P1

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Every infinite-dimensional complex normed space has a toroidally separated
sequence of unit vectors with one strictly positive uniform margin.

The completion-and-density reduction handles general normed spaces. The
nonreflexive case uses the complex Rosenthal dichotomy. For an actual
nontrivial weakly Cauchy sequence, normalized successive differences are
weakly null, and the proved complex unit-modulus suppression selection
supplies toroidal separation. -/
theorem toroidal_elton_odell (X : Type u) [NormedAddCommGroup X]
    [NormedSpace ℂ X] (hX : ¬ FiniteDimensional ℂ X) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  apply completion_separation_transfer
  have hCompletion := completion_infiniteDimensional hX
  by_cases hRef : SurveyStatements.P4.IsReflexiveNormedSpace ℂ (UniformSpace.Completion X)
  · exact reflexive_toroidal_elton_odell hCompletion hRef
  · by_cases hL1 : ∃ S : Submodule ℂ (UniformSpace.Completion X),
        Nonempty (ComplexL1 ≃L[ℂ] S)
    · obtain ⟨S, ⟨T⟩⟩ := hL1
      exact l1_isomorphicCopy_toroidal_elton_odell S T
    · by_cases hC0 : ∃ S : Submodule ℂ (UniformSpace.Completion X),
          Nonempty (ComplexC0 ≃L[ℂ] S)
      · obtain ⟨S, ⟨T⟩⟩ := hC0
        exact c0_isomorphicCopy_toroidal_elton_odell S T
      · by_cases hStrong : ∃ s : ℕ → UniformSpace.Completion X,
          IsStronglySumming s ∧ ¬ ∃ x : UniformSpace.Completion X,
            ∀ f : UniformSpace.Completion X →L[ℂ] ℂ,
              Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds (f x))
        · obtain ⟨s, hs, hnot⟩ := hStrong
          exact stronglySumming_toroidal_elton_odell hs hnot
        · obtain ⟨s, hsNorm, hNoWeakSubsequence⟩ :=
            nonreflexive_exists_bounded_no_weakly_convergent_subsequence hRef
          rcases complex_rosenthal_l1_or_weakCauchy s hsNorm with hL1seq | hWeakCauchy
          · obtain ⟨ν, hν, L, hL, hlower, hupper⟩ := hL1seq
            exact l1_equivalent_sequence_toroidal_elton_odell (s ∘ ν) hL hlower hupper
          · obtain ⟨ν, hν, hWeakCauchy⟩ := hWeakCauchy
            have hnot : ¬ ∃ x : UniformSpace.Completion X,
                ∀ f : UniformSpace.Completion X →L[ℂ] ℂ,
                  Filter.Tendsto (fun n => f ((s ∘ ν) n)) Filter.atTop (nhds (f x)) := by
              rintro ⟨x, hx⟩
              exact hNoWeakSubsequence ⟨ν, hν, x, hx⟩
            exact nontrivial_weakCauchy_toroidal_elton_odell hWeakCauchy hnot

end SurveyStatements.P1
