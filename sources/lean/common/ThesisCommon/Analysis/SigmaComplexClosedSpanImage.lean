import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Normed.Operator.Basic

/-! A continuous linear map on a closed generated span takes values in a
closed submodule whenever it does so on all generators. -/
noncomputable section
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem complexClosedSpan_map_mem (S : Set E)
    (φ : (Submodule.span ℂ S).topologicalClosure →L[ℂ] F)
    (M : Submodule ℂ F) (hM : IsClosed (M : Set F))
    (h : ∀ x (hx : x ∈ S),
      φ ⟨x,Submodule.le_topologicalClosure _ (Submodule.subset_span hx)⟩ ∈ M)
    (x : (Submodule.span ℂ S).topologicalClosure) : φ x ∈ M := by
  let V := (Submodule.span ℂ S).topologicalClosure
  let K := M.comap φ.toLinearMap
  let H := K.map V.subtype
  have hclosed : IsClosed (H : Set E) :=
    (Submodule.isClosed_topologicalClosure _).isClosedMap_subtype_val _ (hM.preimage φ.continuous)
  have hV : V ≤ H := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro y hy
      exact ⟨⟨y,Submodule.le_topologicalClosure _ (Submodule.subset_span hy)⟩,h y hy,rfl⟩
    · exact hclosed
  obtain ⟨y,hy,hyx⟩ := hV x.property
  have heq : y = x := Subtype.ext hyx
  rw [heq] at hy
  exact hy

end ThesisCommon


