import ThesisCommon.Analysis.JamesTreeDelayedCoordinates
import ThesisCommon.Analysis.JamesTreeFiniteMasks

/-! The selected-tree projection has exactly the closed span of the selected
unit vectors as its range. Thus the retraction is onto the actual subspace
appearing in the subtree argument, with no abstract copy substituted. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeDelayedSpan (e : DyadicDelayedFork) :
    Submodule 𝕜 (SegmentJamesTreeSpace 𝕜 p S) :=
  (Submodule.span 𝕜 (Set.range fun s => jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) (e.node s))).topologicalClosure

theorem jamesTreeDelayedInsert_range_closed (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    IsClosed (LinearMap.range (jamesTreeDelayedInsert (𝕜 := 𝕜) (p := p) e hS).toLinearMap :
      Set (SegmentJamesTreeSpace 𝕜 p S)) := by
  have heq : (LinearMap.range (jamesTreeDelayedInsert (𝕜 := 𝕜) (p := p) e hS).toLinearMap :
      Set (SegmentJamesTreeSpace 𝕜 p S)) =
      {x | jamesTreeDelayedProjection e hS x = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact jamesTreeDelayedProjection_insert e hS y
    · intro hx
      exact ⟨jamesTreeDelayedRead e hS x, hx⟩
  rw [heq]
  exact isClosed_eq (jamesTreeDelayedProjection e hS).continuous continuous_id

theorem jamesTreeDelayedInsert_mem_span (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeDelayedInsert e hS x ∈ jamesTreeDelayedSpan e := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage
      (jamesTreeDelayedInsert e hS).continuous
  · intro a
    induction a using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
    | add a b ha hb =>
      simp only [map_add]
      exact Submodule.add_mem _ ha hb
    | single t c =>
      change jamesTreeDelayedInsert e hS
        (jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.single t c)) ∈ _
      rw [jamesTree_dense_smul_unit, map_smul, jamesTreeDelayedInsert_unit]
      exact Submodule.smul_mem _ _
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩))

theorem jamesTreeDelayedInsert_range_eq_span (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    LinearMap.range (jamesTreeDelayedInsert (𝕜 := 𝕜) (p := p) e hS).toLinearMap =
      jamesTreeDelayedSpan e := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact jamesTreeDelayedInsert_mem_span e hS x
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact ⟨jamesTreeUnit s, jamesTreeDelayedInsert_unit e hS s⟩
    · exact jamesTreeDelayedInsert_range_closed e hS

theorem jamesTreeDelayedProjection_range_eq_span (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    LinearMap.range (jamesTreeDelayedProjection (𝕜 := 𝕜) (p := p) e hS).toLinearMap =
      jamesTreeDelayedSpan e := by
  rw [jamesTreeDelayedProjection_range, jamesTreeDelayedInsert_range_eq_span]

def jamesTreeDelayedSpanIsometry (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S ≃ₗᵢ[𝕜] jamesTreeDelayedSpan (𝕜 := 𝕜) (p := p) (S := S) e := by
  rw [← jamesTreeDelayedInsert_range_eq_span e hS]
  exact (jamesTreeDelayedIsometry e hS).equivRange

end ThesisCommon
