import SurveyStatements.P1Geometry
import SurveyStatements.P1BasicSequences
import SurveyStatements.P1PhaseCompactness
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Monotone.Basic

/-!
The finite maximal-family mechanism used in the rapid flat-block alternative:
absence of an infinite separated sequence forces a finite toroidal covering.
The centers belong to the set being covered.
-/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- If there is no infinite sequence in a set with pairwise toroidal distance
strictly above `σ`, finitely many members cover the set with radius `σ`. -/
theorem finite_toroidal_cover (S : Set X) (σ : ℝ)
    (hS : ¬ ∃ x : ℕ → X, (∀ n, x n ∈ S) ∧
      ∀ n m, n ≠ m → σ < toroidalDistance (x n) (x m)) :
    ∃ F : Finset S, ∀ x : S, ∃ y ∈ F, toroidalDistance (x : X) (y : X) ≤ σ := by
  classical
  by_contra hcover
  have hnext : ∀ F : Finset S, ∃ x : S,
      ∀ y ∈ F, σ < toroidalDistance (x : X) (y : X) := by
    intro F
    have h := not_exists.mp hcover F
    simp only [not_forall, not_exists, not_and, not_le] at h
    exact h
  choose next hnextaway using hnext
  let F : ℕ → Finset S := Nat.rec ∅ (fun _ f => insert (next f) f)
  have hF : ∀ n, F (n + 1) = insert (next (F n)) (F n) := fun _ => rfl
  have hmono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hF]
    exact Finset.subset_insert _ _
  let x : ℕ → S := fun n => next (F n)
  have hxmem : ∀ n, x n ∈ F (n + 1) := by
    intro n
    rw [hF]
    exact Finset.mem_insert_self _ _
  have hpair : ∀ n m, n < m → σ < toroidalDistance (x m : X) (x n : X) := by
    intro n m hnm
    apply hnextaway (F m) (x n)
    exact hmono hnm (hxmem n)
  apply hS
  refine ⟨fun n => (x n : X), fun n => (x n).property, ?_⟩
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · rw [toroidalDistance_symm]
    exact hpair n m hlt
  · exact hpair m n hgt

/-- Apply the greedy covering lemma to the actual flat unit blocks in the
closed span, under the no-separation hypothesis of the rapid alternative. -/
theorem finite_etaFlatUnitBlock_cover (e : ℕ → X) {η : ℝ} (hη : 0 < η)
    (hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n m, n ≠ m → 1 + ε < toroidalDistance (x n) (x m)) :
    ∃ F : Finset {b : X // IsEtaFlatUnitBlock e η b},
      ∀ x : {b : X // IsEtaFlatUnitBlock e η b},
        ∃ y ∈ F, toroidalDistance (x : X) (y : X) ≤ 1 + η := by
  apply finite_toroidal_cover {b : X | IsEtaFlatUnitBlock e η b} (1 + η)
  rintro ⟨x, hx, hs⟩
  apply hno η hη
  refine ⟨x, ?_, hs⟩
  intro n
  exact ⟨etaFlatUnitBlock_mem_closedSpan (hx n), norm_etaFlatUnitBlock (hx n)⟩

/-- The covering conclusion in the exact phase form used in the backward
recursion of the source rapid alternative. -/
theorem finite_etaFlatUnitBlock_phase_cover (e : ℕ → X) {η : ℝ} (hη : 0 < η)
    (hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n m, n ≠ m → 1 + ε < toroidalDistance (x n) (x m)) :
    ∃ F : Finset {b : X // IsEtaFlatUnitBlock e η b},
      ∀ x : {b : X // IsEtaFlatUnitBlock e η b},
        ∃ y ∈ F, ∃ θ ∈ unitScalars, ‖(x : X) - θ • (y : X)‖ ≤ 1 + η := by
  obtain ⟨F, hF⟩ := finite_etaFlatUnitBlock_cover e hη hno
  refine ⟨F, ?_⟩
  intro x
  obtain ⟨y, hy, hd⟩ := hF x
  exact ⟨y, hy, (toroidalDistance_le_iff_exists_phase _ _ _).mp hd⟩

end SurveyStatements.P1
