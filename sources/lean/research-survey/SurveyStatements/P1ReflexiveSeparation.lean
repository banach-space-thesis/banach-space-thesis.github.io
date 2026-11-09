import SurveyStatements.P1RapidCovers
import SurveyStatements.P1RapidAlternative
import SurveyStatements.P1OrderedBlockObstruction
import SurveyStatements.P1ReflexiveCompleteness

/-!
The rapid alternative proves toroidal Elton--Odell for reflexive spaces.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The boundedly complete branch is closed for an asymptotically monotone
sequence with the direct construction's uniform projection estimate. -/
theorem separation_of_boundedlyComplete_asymptoticallyMonotone
    {e : ℕ → X} (he : IsAsymptoticallyMonotone e)
    (hc : IsBoundedlyComplete e)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  classical
  by_contra hsep
  have hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n k, n ≠ k → 1 + ε < toroidalDistance (x n) (x k) := by
    intro ε hε
    rintro ⟨x, hx, hdist⟩
    apply hsep
    refine ⟨ε, hε, x, fun n => (hx n).2, ?_⟩
    intro n k hnk θ hθ
    exact (hdist n k hnk).le.trans (toroidalDistance_le_phase _ _ hθ)
  obtain ⟨coverData⟩ := exists_rapidCoverData e he rapidEta rapidEta
    rapidEta_pos rapidEta_pos hno
  obtain ⟨b, α, hb, hα, _, hnorm, hbound⟩ := rapid_flatBlocks_of_covers e coverData
  have hs : ∀ n i, i ∈ (b n).support →
      coverData.m n ≤ i ∧ i < coverData.m (n + 1) :=
    fun n i hi => coverData.support n (b n) (hb n) i hi
  exact boundedlyComplete_uniform_orderedBlock_obstruction hc (by norm_num) hp
    coverData.m coverData.strictMono b hs α hα hnorm hbound

/-- Toroidal Elton--Odell in every infinite-dimensional reflexive complex
normed space. The reflexivity notion is surjectivity into the bidual. -/
theorem reflexive_toroidal_elton_odell (hX : ¬ FiniteDimensional ℂ X)
    (hRef : SurveyStatements.P4.IsReflexiveNormedSpace ℂ X) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  obtain ⟨e, he, hc, hp⟩ := reflexive_exists_asymptoticallyMonotone_boundedlyComplete hX hRef
  exact separation_of_boundedlyComplete_asymptoticallyMonotone he hc hp

end SurveyStatements.P1
