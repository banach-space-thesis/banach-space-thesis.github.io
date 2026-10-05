import ThesisCommon.Analysis.SchauderOperators
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! The closed range of a norm-preserving basis operator is exactly the
closed span of its basis images. This supplies the actual isometric-span
identification in subtree arguments.
-/
noncomputable section
open Filter Topology
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (b : NormalizedSchauderBasis 𝕜 X)

theorem isometric_range_eq_closed_span (B : X →L[𝕜] Y) (hB : ∀ x, ‖B x‖ = ‖x‖) :
    LinearMap.range B.toLinearMap =
      (Submodule.span 𝕜 (Set.range (fun n => B (b.vector n)))).topologicalClosure := by
  let L : X →ₗᵢ[𝕜] Y := { B.toLinearMap with norm_map' := hB }
  let S := Submodule.span 𝕜 (Set.range (fun n => B (b.vector n)))
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    have ht := (B.continuous.tendsto x).comp (b.expansion x)
    apply S.isClosed_topologicalClosure.mem_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro N
    change B (∑ n ∈ Finset.range N, b.coord n x • b.vector n) ∈ S.topologicalClosure
    rw [map_sum]
    apply Submodule.sum_mem
    intro n _
    rw [map_smul]
    exact S.le_topologicalClosure (S.smul_mem _ (Submodule.subset_span ⟨n, rfl⟩))
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro y ⟨n, rfl⟩
      exact ⟨b.vector n, rfl⟩
    · exact L.isometry.isClosedEmbedding.isClosed_range

theorem nonempty_equiv_closed_span (B : X →L[𝕜] Y) (hB : ∀ x, ‖B x‖ = ‖x‖) :
    Nonempty (X ≃ₗᵢ[𝕜]
      (Submodule.span 𝕜 (Set.range (fun n => B (b.vector n)))).topologicalClosure) := by
  let L : X →ₗᵢ[𝕜] Y := { B.toLinearMap with norm_map' := hB }
  exact ⟨L.equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (b.isometric_range_eq_closed_span B hB))⟩

end NormalizedSchauderBasis
end ThesisCommon
