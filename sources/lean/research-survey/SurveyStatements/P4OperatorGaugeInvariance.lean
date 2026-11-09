import SurveyStatements.P4DFJPOperatorFactorization

/-! Genuine invariance of the operator-generated interpolation set under
an intertwining contraction on its domain. -/

noncomputable section
set_option autoImplicit false

open Set Metric

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

theorem operatorGaugeData_preserved (T : X →L[𝕜] E) (S : E →L[𝕜] E)
    (U : X →L[𝕜] X) (hU : ‖U‖ ≤ 1) (hcomp : S.comp T = T.comp U) :
    ∀ x ∈ (operatorGaugeData T).carrier, S x ∈ (operatorGaugeData T).carrier := by
  intro x hx
  apply closure_minimal ?_ (isClosed_closure.preimage S.continuous) hx
  rintro y ⟨z, hz, rfl⟩
  apply subset_closure
  refine ⟨U z, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact (U.le_opNorm z).trans ((mul_le_mul hU (mem_closedBall_zero_iff.mp hz)
      (norm_nonneg z) (by norm_num)).trans_eq (one_mul _))
  · exact (congrArg (fun B : X →L[𝕜] E => B z) hcomp).symm

theorem operatorGaugeData_closedSpan_maps_into (T : X →L[𝕜] E) (S : E →L[𝕜] E)
    (F : Submodule 𝕜 E) (hF : IsClosed (F : Set E)) (hST : ∀ x : X, S (T x) ∈ F) :
    ∀ y ∈ closure (Submodule.span 𝕜 (operatorGaugeData T).carrier : Set E), S y ∈ F := by
  let P := F.comap S.toLinearMap
  have hP : IsClosed (P : Set E) := hF.preimage S.continuous
  have hcarrier : (operatorGaugeData T).carrier ⊆ P := by
    apply closure_minimal ?_ hP
    rintro y ⟨x, hx, rfl⟩
    exact hST x
  have hspan : (Submodule.span 𝕜 (operatorGaugeData T).carrier : Set E) ⊆ P :=
    Submodule.span_le.mpr hcarrier
  exact fun y hy => closure_minimal hspan hP hy

end SurveyStatements.P4
