import SurveyStatements.P4Gantmacher
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Finite Goldstine approximation and norm-bounded annihilators, used to
construct a bounded sequence with no weakly convergent subsequence in a
nonreflexive Banach space. No sequential compactness assertion is assumed. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem goldstine_finite_approximation (ξ : StrongDual ℂ (StrongDual ℂ X))
    (hξ : ‖ξ‖ ≤ 1) (F : Finset (StrongDual ℂ X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ ∀ f ∈ F, ‖f x - ξ f‖ < ε := by
  classical
  let U : Set (WeakDual ℂ (StrongDual ℂ X)) :=
    ⋂ f ∈ F, {η | ‖η f - ξ f‖ < ε}
  have hU : IsOpen U := isOpen_biInter_finset fun f _ =>
    isOpen_lt ((WeakDual.eval_continuous f).sub continuous_const).norm continuous_const
  have hξU : StrongDual.toWeakDual ξ ∈ U := by
    simp only [U, mem_iInter, mem_setOf_eq]
    intro f _
    simpa using hε
  obtain ⟨η, hηU, x, hx, hη⟩ := mem_closure_iff.mp
    (SurveyStatements.P4.goldstine_unitBall ξ hξ) U hU hξU
  refine ⟨x, by simpa using hx, ?_⟩
  intro f hf
  have h := (mem_iInter.mp (mem_iInter.mp hηU f) hf)
  rw [← hη] at h
  exact h

theorem closedSubmodule_exists_bounded_annihilator (S : Submodule ℂ X)
    (hS : IsClosed (S : Set X)) {x : X} (hx : x ∉ S) :
    ∃ f : StrongDual ℂ X, ‖f‖ ≤ 1 ∧ (∀ y ∈ S, f y = 0) ∧ f x ≠ 0 := by
  letI : IsClosed (S : Set X) := hS
  let q : X →L[ℂ] X ⧸ S := S.mkQ.mkContinuous 1 (fun y => by
    simpa using Submodule.Quotient.norm_mk_le (S := S) y)
  have hqx : q x ≠ 0 := by
    change Submodule.Quotient.mk x ≠ (0 : X ⧸ S)
    exact mt (Submodule.Quotient.mk_eq_zero S).mp hx
  obtain ⟨g, hgnorm, hgx⟩ := exists_dual_vector ℂ (q x) hqx
  refine ⟨g.comp q, ?_, ?_, ?_⟩
  · have hq : ‖q‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa only [hgnorm, one_mul] using hq)
  · intro y hy
    have hqy : q y = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hy
    simp only [ContinuousLinearMap.comp_apply, hqy, map_zero]
  · change g (q x) ≠ 0
    rw [hgx]
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hqx)

end SurveyStatements.P1
