import SurveyStatements.P2Definitions
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Linarith

/-! Operators induced on a closed invariant subspace quotient, including the correction bound. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P2
universe v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]

def quotientProjection (N : Submodule ℂ X) : X →L[ℂ] X ⧸ N :=
  N.mkQ.mkContinuous 1 (fun x => by simpa only [one_mul] using Submodule.Quotient.norm_mk_le N x)

@[simp] theorem quotientProjection_apply (N : Submodule ℂ X) (x : X) :
    quotientProjection N x = N.mkQ x := rfl

theorem quotientLinearMap_bound (N : Submodule ℂ X) (T : BoundedOperators X)
    (hT : N ≤ N.comap T.toLinearMap) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : X, ‖N.mkQ (T x)‖ ≤ C * ‖x‖) (y : X ⧸ N) :
    ‖N.mapQ N T.toLinearMap hT y‖ ≤ C * ‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hdenom : 0 < C + 1 := by linarith
  have hδ : 0 < ε / (C + 1) := div_pos hε hdenom
  obtain ⟨x, hx, hnx⟩ := Submodule.Quotient.norm_mk_lt y hδ
  have hnorm : ‖N.mapQ N T.toLinearMap hT y‖ ≤ C * ‖x‖ := by
    rw [← hx]
    exact hbound x
  have hδeq : ε / (C + 1) * (C + 1) = ε := div_mul_cancel₀ ε hdenom.ne'
  nlinarith

def quotientEndomorphism (N : Submodule ℂ X) (T : BoundedOperators X)
    (hT : N ≤ N.comap T.toLinearMap) : (X ⧸ N) →L[ℂ] (X ⧸ N) :=
  (N.mapQ N T.toLinearMap hT).mkContinuous ‖T‖
    (quotientLinearMap_bound N T hT ‖T‖ (norm_nonneg T)
      (fun x => (Submodule.Quotient.norm_mk_le N (T x)).trans (T.le_opNorm x)))

@[simp] theorem quotientEndomorphism_mk (N : Submodule ℂ X) (T : BoundedOperators X)
    (hT : N ≤ N.comap T.toLinearMap) (x : X) :
    quotientEndomorphism N T hT (N.mkQ x) = N.mkQ (T x) := rfl

theorem norm_quotientEndomorphism_le (N : Submodule ℂ X) (T : BoundedOperators X)
    (hT : N ≤ N.comap T.toLinearMap) : ‖quotientEndomorphism N T hT‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    (quotientLinearMap_bound N T hT ‖T‖ (norm_nonneg T)
      (fun x => (Submodule.Quotient.norm_mk_le N (T x)).trans (T.le_opNorm x)))

/-- A correction whose range lies in the killed subspace also bounds the induced norm. -/
theorem norm_quotientEndomorphism_le_correction (N : Submodule ℂ X)
    (T K : BoundedOperators X) (hT : N ≤ N.comap T.toLinearMap)
    (hK : ∀ x : X, K x ∈ N) : ‖quotientEndomorphism N T hT‖ ≤ ‖T + K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (T + K))
  apply quotientLinearMap_bound N T hT ‖T + K‖ (norm_nonneg (T + K))
  intro x
  have heq : N.mkQ (T x) = N.mkQ ((T + K) x) := by
    simp only [ContinuousLinearMap.add_apply, map_add]
    have hz : N.mkQ (K x) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (hK x)
    rw [hz, add_zero]
  rw [heq]
  exact (Submodule.Quotient.norm_mk_le N _).trans ((T + K).le_opNorm x)

/-- Products descend to the actual composition on the quotient. -/
theorem quotientEndomorphism_mul (N : Submodule ℂ X) (S T : BoundedOperators X)
    (hS : N ≤ N.comap S.toLinearMap) (hT : N ≤ N.comap T.toLinearMap)
    (hST : N ≤ N.comap (S * T).toLinearMap) :
    quotientEndomorphism N (S * T) hST =
      quotientEndomorphism N S hS * quotientEndomorphism N T hT := by
  ext y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
  simp only [quotientEndomorphism_mk, ContinuousLinearMap.mul_apply]

theorem quotientEndomorphism_sum (N : Submodule ℂ X) (U : ℕ → BoundedOperators X)
    (hU : ∀ j, N ≤ N.comap (U j).toLinearMap) (F : Finset ℕ) (a : ℕ → ℂ)
    (hsum : N ≤ N.comap (∑ j ∈ F, a j • U j).toLinearMap) :
    quotientEndomorphism N (∑ j ∈ F, a j • U j) hsum =
      ∑ j ∈ F, a j • quotientEndomorphism N (U j) (hU j) := by
  ext y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
  simp only [quotientEndomorphism_mk, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul]

end SurveyStatements.P2
