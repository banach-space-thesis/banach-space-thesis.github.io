import ThesisCommon.Analysis.JamesTreeSelectedCoordinates
import ThesisCommon.Analysis.JamesTreeFiniteMasks

/-! The selected-tree projection has exactly the closed span of the selected
unit vectors as its range. Thus the retraction is onto the actual subspace
appearing in the subtree argument, with no abstract copy substituted. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeSelectedSpan (e : DyadicSubtreeEmbedding) :
    Submodule 𝕜 (SegmentJamesTreeSpace 𝕜 p S) :=
  (Submodule.span 𝕜 (Set.range fun s => jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) (e s))).topologicalClosure

theorem jamesTreeSelectedInsert_range_closed (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    IsClosed (LinearMap.range (jamesTreeSelectedInsert (𝕜 := 𝕜) (p := p) e hS).toLinearMap :
      Set (SegmentJamesTreeSpace 𝕜 p S)) := by
  have heq : (LinearMap.range (jamesTreeSelectedInsert (𝕜 := 𝕜) (p := p) e hS).toLinearMap :
      Set (SegmentJamesTreeSpace 𝕜 p S)) =
      {x | jamesTreeSelectedProjection e hS x = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact jamesTreeSelectedProjection_insert e hS y
    · intro hx
      exact ⟨jamesTreeSelectedRead e hS x, hx⟩
  rw [heq]
  exact isClosed_eq (jamesTreeSelectedProjection e hS).continuous continuous_id

theorem jamesTreeSelectedInsert_mem_span (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeSelectedInsert e hS x ∈ jamesTreeSelectedSpan e := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage
      (jamesTreeSelectedInsert e hS).continuous
  · intro a
    induction a using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
    | add a b ha hb =>
      simp only [map_add]
      exact Submodule.add_mem _ ha hb
    | single t c =>
      change jamesTreeSelectedInsert e hS
        (jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.single t c)) ∈ _
      rw [jamesTree_dense_smul_unit, map_smul, jamesTreeSelectedInsert_unit]
      exact Submodule.smul_mem _ _
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩))

theorem jamesTreeSelectedInsert_range_eq_span (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    LinearMap.range (jamesTreeSelectedInsert (𝕜 := 𝕜) (p := p) e hS).toLinearMap =
      jamesTreeSelectedSpan e := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact jamesTreeSelectedInsert_mem_span e hS x
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact ⟨jamesTreeUnit s, jamesTreeSelectedInsert_unit e hS s⟩
    · exact jamesTreeSelectedInsert_range_closed e hS

theorem jamesTreeSelectedProjection_range_eq_span (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    LinearMap.range (jamesTreeSelectedProjection (𝕜 := 𝕜) (p := p) e hS).toLinearMap =
      jamesTreeSelectedSpan e := by
  rw [jamesTreeSelectedProjection_range, jamesTreeSelectedInsert_range_eq_span]

def jamesTreeSelectedSpanIsometry (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S ≃ₗᵢ[𝕜] jamesTreeSelectedSpan (𝕜 := 𝕜) (p := p) (S := S) e := by
  rw [← jamesTreeSelectedInsert_range_eq_span e hS]
  exact (jamesTreeSelectedIsometry e hS).equivRange

end ThesisCommon
