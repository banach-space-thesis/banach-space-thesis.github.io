import ThesisCommon.Analysis.Gantmacher

/-! The genuine weakly compact operator ideal is norm closed when the
range space is complete. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
open Set Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem continuous_bidualMap_apply (ξ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    Continuous (fun T : E →L[𝕜] F => bidualMap T ξ) := by
  exact (((ContinuousLinearMap.compL 𝕜 (StrongDual 𝕜 F) (StrongDual 𝕜 E) 𝕜) ξ).comp
    (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip).continuous

theorem isClosed_bidualImage [CompleteSpace F] :
    IsClosed (bidualImage 𝕜 F : Set (StrongDual 𝕜 (StrongDual 𝕜 F))) := by
  have hJ : Topology.IsClosedEmbedding
      (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := F)) :=
    Isometry.isClosedEmbedding (α := F) (γ := StrongDual 𝕜 (StrongDual 𝕜 F))
      (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := F)).isometry
  exact hJ.isClosed_range

theorem isClosed_weaklyCompactSubmodule [CompleteSpace F] :
    IsClosed (weaklyCompactSubmodule 𝕜 E F : Set (E →L[𝕜] F)) := by
  have heq : (weaklyCompactSubmodule 𝕜 E F : Set (E →L[𝕜] F)) =
      ⋂ ξ : StrongDual 𝕜 (StrongDual 𝕜 E), {T | bidualMap T ξ ∈ bidualImage 𝕜 F} := by
    ext T
    simpa only [Set.mem_iInter, Set.mem_setOf_eq] using gantmacher_iff_bidual_mem_image T
  rw [heq]
  exact isClosed_iInter fun ξ => (isClosed_bidualImage (𝕜 := 𝕜) (F := F)).preimage
    (continuous_bidualMap_apply (𝕜 := 𝕜) (E := E) (F := F) ξ)

end ThesisCommon
