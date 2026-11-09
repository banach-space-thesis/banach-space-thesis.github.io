import SurveyStatements.P1StronglySummingSelection
import SurveyStatements.P1FlatScalarObstruction
import SurveyStatements.P1PairedCoefficients

/-! The complete strongly summing case from the source. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A nontrivial strongly summing sequence gives toroidal Elton--Odell.
The paired scalar expansion is performed in the original sequence and uses
its genuine strongly summing property. -/
theorem stronglySumming_toroidal_elton_odell {s : ℕ → X}
    (hs : IsStronglySumming s)
    (hnot : ¬ ∃ x : X, ∀ f : X →L[ℂ] ℂ,
      Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  classical
  obtain ⟨r, hr, p, q, hpair, hlower, he, hp⟩ :=
    weakCauchy_nonconvergent_asymptoticallyMonotone_pairs hs.2.1 hnot
  let e : ℕ → X := fun n => unitNormalize (s (p n) - s (q n))
  obtain ⟨M, hM⟩ := weakCauchy_norm_bounded hs.2.1
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
  obtain ⟨a, ha, hbound, hnonzero⟩ :=
    exists_bounded_nonvanishing_flat_coefficients he hp hno
  have hpaired : HasBoundedPartialSums s (normalizedPairCoefficients s p q a) :=
    normalizedPairCoefficients_bounded s p q hpair hr hlower hM a ha hbound
  have hc := stronglySumming_coefficients_tendsto_zero hs hpaired
  exact hnonzero (normalizedPairCoefficients_tendsto_zero_imp s p q hpair hr hlower hM a hc)

end SurveyStatements.P1
