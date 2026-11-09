import SurveyStatements.P4DFJPLift
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-! Genuine DFJP reflexive factorization of any weakly compact operator. -/

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Pointwise

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {X : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

lemma operator_unitBall_absConvex (T : X →L[𝕜] E) :
    AbsConvex 𝕜 (T '' closedBall (0 : X) 1) := by
  refine ⟨?_, ?_⟩
  · apply balanced_iff_smul_mem.mpr
    intro a ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨a • x, ?_, map_smul T a x⟩
    rw [mem_closedBall_zero_iff, norm_smul]
    exact (mul_le_mul ha (mem_closedBall_zero_iff.mp hx)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · exact (convex_closedBall (0 : X) 1).linear_image (T.restrictScalars ℝ).toLinearMap

def operatorGaugeData (T : X →L[𝕜] E) : DFJPGaugeData 𝕜 E where
  carrier := closure (T '' closedBall (0 : X) 1)
  absConvex := (operator_unitBall_absConvex T).closure
  zero_mem := subset_closure ⟨0, by simp, map_zero T⟩
  normBound := ‖T‖
  normBound_nonneg := norm_nonneg T
  norm_le := by
    apply closure_minimal ?_ isClosed_closedBall
    rintro y ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact (T.le_opNorm x).trans ((mul_le_mul_of_nonneg_left
      (mem_closedBall_zero_iff.mp hx) (norm_nonneg T)).trans_eq (mul_one _))

lemma operatorGaugeData_weakCompact (T : X →L[𝕜] E)
    (hT : IsWeaklyCompactOperator 𝕜 T) :
    IsCompact ((toWeakSpace 𝕜 E) '' (operatorGaugeData T).carrier) := by
  change IsCompact ((toWeakSpace 𝕜 E) '' closure (T '' closedBall (0 : X) 1))
  rw [(operator_unitBall_absConvex T).2.toWeakSpace_closure 𝕜]
  exact hT

/-- Every weakly compact map factors through the actual reflexive DFJP gauge
space. The basis requirement in the survey main is a further obligation. -/
theorem dfjp_reflexive_factorization [CompleteSpace E] (T : X →L[𝕜] E)
    (hT : IsWeaklyCompactOperator 𝕜 T) :
    ∃ D : DFJPGaugeData 𝕜 E, IsReflexiveNormedSpace 𝕜 (DFJPSpace D) ∧
      ∃ A : X →L[𝕜] DFJPSpace D, (DFJPSpace.inclusion D).comp A = T := by
  let D := operatorGaugeData T
  have hunit : ∀ x : X, ‖x‖ ≤ 1 → T x ∈ D.carrier := by
    intro x hx
    exact subset_closure ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
  refine ⟨D, DFJPSpace.reflexive D (operatorGaugeData_weakCompact T hT),
    DFJPSpace.lift D T hunit, DFJPSpace.inclusion_comp_lift D T hunit⟩

end SurveyStatements.P4
