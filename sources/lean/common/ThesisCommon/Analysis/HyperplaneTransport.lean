import ThesisCommon.Analysis.HyperplaneScalarExtension

/-! Transport of genuine closed codimension-one subspaces under bounded
linear isomorphisms. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local instance hyperplaneTransportBidualGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance hyperplaneTransportBidualSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

def continuousSubmoduleImageEquiv (e : E ≃L[𝕜] F) (H : Submodule 𝕜 E) :
    H ≃L[𝕜] H.map e.toLinearEquiv.toLinearMap :=
  { e.toLinearEquiv.submoduleMap H with
    continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

theorem IsClosedHyperplane.map {H : Submodule 𝕜 E}
    (hH : IsClosedHyperplane 𝕜 E H) (e : E ≃L[𝕜] F) :
    IsClosedHyperplane 𝕜 F (H.map e.toLinearEquiv.toLinearMap) := by
  refine ⟨?_, ?_⟩
  · change IsClosed (e '' (H : Set E))
    exact e.isClosed_image.mpr hH.1
  · let a := Submodule.Quotient.equiv H (H.map e.toLinearEquiv.toLinearMap)
      e.toLinearEquiv rfl
    apply Module.rank_eq_one_iff_finrank_eq_one.mpr
    rw [← a.finrank_eq]
    exact Module.rank_eq_one_iff_finrank_eq_one.mp hH.2

/-- If E has order one and its bidual is isomorphic to a space F which is
isomorphic to every hyperplane, then E is isomorphic to F. -/
theorem nonempty_equiv_of_bidual_equiv [CompleteSpace E]
    (hE : IsQuasiReflexiveOfOrderOne 𝕜 E)
    (hF : IsIsomorphicToEveryHyperplane 𝕜 F)
    (e : StrongDual 𝕜 (StrongDual 𝕜 E) ≃L[𝕜] F) : Nonempty (E ≃L[𝕜] F) := by
  let H := (bidualImage 𝕜 E).map e.toLinearEquiv.toLinearMap
  obtain ⟨a⟩ := hF H (hE.bidualHyperplane.map e)
  let k : E ≃L[𝕜] bidualImage 𝕜 E := canonicalBidualImageEquiv (𝕜 := 𝕜) (X := E)
  let i : bidualImage 𝕜 E ≃L[𝕜] H :=
    continuousSubmoduleImageEquiv (𝕜 := 𝕜)
      (E := StrongDual 𝕜 (StrongDual 𝕜 E)) (F := F) e (bidualImage 𝕜 E)
  exact ⟨k.trans (i.trans a.symm)⟩

end ThesisCommon
