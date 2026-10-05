import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Normed.Operator.Basic

/-! Functionals on a closed generated subspace are determined by generators. -/
noncomputable section
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closedSpan_dual_ext (S : Set E)
    (φ ψ : (Submodule.span ℝ S).topologicalClosure →L[ℝ] ℝ)
    (h : ∀ x (hx : x ∈ S),
      φ ⟨x,Submodule.le_topologicalClosure _ (Submodule.subset_span hx)⟩ =
      ψ ⟨x,Submodule.le_topologicalClosure _ (Submodule.subset_span hx)⟩) : φ = ψ := by
  let V := (Submodule.span ℝ S).topologicalClosure
  let K := LinearMap.ker (φ - ψ).toLinearMap
  let H := K.map V.subtype
  have hclosed : IsClosed (H : Set E) :=
    (Submodule.isClosed_topologicalClosure _).isClosedMap_subtype_val _
      (isClosed_eq (φ - ψ).continuous continuous_const)
  have hV : V ≤ H := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro x hx
      refine ⟨⟨x,Submodule.le_topologicalClosure _ (Submodule.subset_span hx)⟩,?_,rfl⟩
      change φ _ - ψ _ = 0
      exact sub_eq_zero.mpr (h x hx)
    · exact hclosed
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y,hy,hyx⟩ := hV x.property
  have heq : y = x := Subtype.ext hyx
  rw [heq] at hy
  exact sub_eq_zero.mp hy

end ThesisCommon
