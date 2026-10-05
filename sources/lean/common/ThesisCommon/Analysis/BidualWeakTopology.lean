import ThesisCommon.Residuum
import ThesisCommon.WeakCompact

/-! The canonical bidual embedding and the bidual operator with their
actual weak and weak-star topologies. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
open Set Topology TopologicalSpace
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def weakBidualInclusion : WeakSpace 𝕜 E →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 E) where
  toLinearMap := (StrongDual.toWeakDual.toLinearMap.comp
    (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap).comp (toWeakSpace 𝕜 E).symm.toLinearMap
  cont := by
    apply WeakDual.continuous_of_continuous_eval
    intro f
    exact WeakBilin.eval_continuous _ f

theorem weakBidualInclusion_apply (x : WeakSpace 𝕜 E) (f : StrongDual 𝕜 E) :
    weakBidualInclusion x f = f ((toWeakSpace 𝕜 E).symm x) := rfl

theorem isEmbedding_weakBidualInclusion :
    IsEmbedding (weakBidualInclusion (𝕜 := 𝕜) (E := E)) := by
  constructor
  · constructor
    change induced (fun x : WeakSpace 𝕜 E => fun f : StrongDual 𝕜 E => f x) Pi.topologicalSpace =
      induced weakBidualInclusion
        (induced (fun ξ : WeakDual 𝕜 (StrongDual 𝕜 E) => fun f : StrongDual 𝕜 E => ξ f)
          Pi.topologicalSpace)
    rw [induced_compose]
    rfl
  · intro x y hxy
    apply (toWeakSpace 𝕜 E).symm.injective
    apply (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).injective
    exact StrongDual.toWeakDual.injective hxy

def weakStarBidualMap (T : E →L[𝕜] F) :
    WeakDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 F) where
  toLinearMap := (StrongDual.toWeakDual.toLinearMap.comp (bidualMap T).toLinearMap).comp
    WeakDual.toStrongDual.toLinearMap
  cont := by
    apply WeakDual.continuous_of_continuous_eval
    intro f
    exact WeakDual.eval_continuous (banachAdjoint T f)

theorem weakStarBidualMap_apply (T : E →L[𝕜] F)
    (ξ : WeakDual 𝕜 (StrongDual 𝕜 E)) (f : StrongDual 𝕜 F) :
    weakStarBidualMap T ξ f = ξ (banachAdjoint T f) := rfl

theorem weakStarBidualMap_inclusion (T : E →L[𝕜] F) (x : E) :
    weakStarBidualMap T (weakBidualInclusion (toWeakSpace 𝕜 E x)) =
      weakBidualInclusion (toWeakSpace 𝕜 F (T x)) := rfl

end ThesisCommon
