import ThesisCommon.Analysis.BanachAdjointNorm

noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

local instance : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

theorem banachAdjoint_add (S T : E →L[𝕜] F) :
    banachAdjoint (S + T) = banachAdjoint S + banachAdjoint T :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip.map_add S T

theorem banachAdjoint_sub (S T : E →L[𝕜] F) :
    banachAdjoint (S - T) = banachAdjoint S - banachAdjoint T :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip.map_sub S T

theorem banachAdjoint_smul (a : 𝕜) (T : E →L[𝕜] F) :
    banachAdjoint (a • T) = a • banachAdjoint T :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip.map_smul a T

theorem bidualMap_add (S T : E →L[𝕜] F) :
    bidualMap (S + T) = bidualMap S + bidualMap T := by
  unfold bidualMap
  rw [banachAdjoint_add, banachAdjoint_add]

theorem bidualMap_sub (S T : E →L[𝕜] F) :
    bidualMap (S - T) = bidualMap S - bidualMap T := by
  unfold bidualMap
  rw [banachAdjoint_sub, banachAdjoint_sub]

theorem bidualMap_smul (a : 𝕜) (T : E →L[𝕜] F) :
    bidualMap (a • T) = a • bidualMap T := by
  unfold bidualMap
  rw [banachAdjoint_smul, banachAdjoint_smul]

theorem bidualMap_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    bidualMap (S.comp T) = (bidualMap S).comp (bidualMap T) := by
  unfold bidualMap
  rw [banachAdjoint_comp, banachAdjoint_comp]

theorem norm_bidualMap (T : E →L[𝕜] F) : ‖bidualMap T‖ = ‖T‖ := by
  unfold bidualMap
  rw [norm_banachAdjoint, norm_banachAdjoint]

end ThesisCommon
