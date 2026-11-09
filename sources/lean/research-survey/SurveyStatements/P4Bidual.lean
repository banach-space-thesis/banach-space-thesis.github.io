import SurveyStatements.P4WeakCompact

/-! Banach adjoints and their canonical weak-star bidual maps, used by
the weak compactness criterion. Definitions have their actual operator norms. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024

open Set Topology

namespace SurveyStatements.P4

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The Banach adjoint acts by precomposition. -/
def banachAdjoint (T : E →L[𝕜] F) : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T

/-- The second adjoint, equipped with the strong bidual norms. -/
def bidualMap (T : E →L[𝕜] F) :
    StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F) :=
  banachAdjoint (banachAdjoint T)

/-- The actual canonical image in the normed bidual. -/
def bidualImage (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  LinearMap.range (NormedSpace.inclusionInDoubleDual 𝕜 E)

def weakStarBidualMap (T : E →L[𝕜] F) :
    WeakDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 F) where
  toLinearMap := (StrongDual.toWeakDual.toLinearMap.comp (bidualMap T).toLinearMap).comp
    WeakDual.toStrongDual.toLinearMap
  cont := by
    apply WeakDual.continuous_of_continuous_eval
    intro f
    exact WeakDual.eval_continuous (banachAdjoint T f)

@[simp] theorem banachAdjoint_apply (T : E →L[𝕜] F) (f : StrongDual 𝕜 F) (x : E) :
    banachAdjoint T f x = f (T x) := rfl

@[simp] theorem bidualMap_apply (T : E →L[𝕜] F)
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 E)) (f : StrongDual 𝕜 F) :
    bidualMap T ξ f = ξ (banachAdjoint T f) := rfl

theorem bidualMap_inclusion (T : E →L[𝕜] F) (x : E) :
    bidualMap T (NormedSpace.inclusionInDoubleDual 𝕜 E x) =
      NormedSpace.inclusionInDoubleDual 𝕜 F (T x) := rfl

theorem bidualMap_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    bidualMap (S.comp T) = (bidualMap S).comp (bidualMap T) := rfl

@[simp] theorem bidualMap_id : bidualMap (ContinuousLinearMap.id 𝕜 E) =
    ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) := by
  ext ξ f
  rfl

end SurveyStatements.P4
