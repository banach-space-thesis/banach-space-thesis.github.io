import SurveyStatements.P1WeakNullSuppression
import SurveyStatements.P1SuccessivePairs

/-! The actual nontrivial weak-Cauchy leaf of the main proof. Successive
norm-separated differences are normalized and weakly null; the proved
unit-modulus suppression selection supplies toroidal separation. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem nontrivial_weakCauchy_toroidal_elton_odell {s : ℕ → X}
    (hs : IsWeakCauchySequence s)
    (hnot : ¬ ∃ x : X, ∀ f : StrongDual ℂ X,
      Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  obtain ⟨r, hr, p, q, hpq, hsep, hnorm, hweak⟩ :=
    weakCauchy_nonconvergent_normalized_successive_pairs hs hnot
  exact normalized_weakNull_toroidal_elton_odell
    (fun n => unitNormalize (s (p n) - s (q n))) hnorm hweak

end SurveyStatements.P1
