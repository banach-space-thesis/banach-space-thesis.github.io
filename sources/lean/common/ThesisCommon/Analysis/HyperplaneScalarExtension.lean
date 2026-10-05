import ThesisCommon.Analysis.ScalarExtensionAbsorption

/-! Converse scalar absorption and the canonical codimension-one bidual
decomposition used in Appendix B.3. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

local instance hyperplaneBidualGroup : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 X)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 X) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance hyperplaneBidualSpace : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 X) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

theorem scalarFunctional_closedHyperplane (f : X →L[𝕜] 𝕜) (hf : f ≠ 0) :
    IsClosedHyperplane 𝕜 X (LinearMap.ker f.toLinearMap) := by
  obtain ⟨u, hu, _⟩ := exists_common_transverse f f hf hf
  have hs : Function.Surjective f := by
    intro a
    refine ⟨(a * (f u)⁻¹) • u, ?_⟩
    simp [map_smul, hu]
  let e := f.toLinearMap.quotKerEquivOfSurjective hs
  exact ⟨ContinuousLinearMap.isClosed_ker f, Module.rank_eq_one_iff_finrank_eq_one.mpr
    (e.finrank_eq.trans (Module.finrank_self 𝕜))⟩

/-- An actual closed hyperplane has a bounded one-dimensional complement. -/
def closedHyperplaneProductEquiv (H : Submodule 𝕜 X) (hH : IsClosedHyperplane 𝕜 X H) :
    X ≃L[𝕜] (H × 𝕜) := by
  let f := hH.exists_functional.choose
  have hf : f ≠ 0 := hH.exists_functional.choose_spec.1
  have hker : LinearMap.ker f.toLinearMap = H := hH.exists_functional.choose_spec.2
  let u := (exists_common_transverse f f hf hf).choose
  have hu : f u ≠ 0 := (exists_common_transverse f f hf hf).choose_spec.1
  let s : 𝕜 →L[𝕜] X := (ContinuousLinearMap.id 𝕜 𝕜).smulRight ((f u)⁻¹ • u)
  have hs : Function.RightInverse s f := by
    intro a
    change f (a • ((f u)⁻¹ • u)) = a
    simp [map_smul, hu]
  have e := ContinuousLinearEquiv.equivOfRightInverse f s hs
  change X ≃L[𝕜] (𝕜 × LinearMap.ker f.toLinearMap) at e
  rw [hker] at e
  exact e.trans (ContinuousLinearEquiv.prodComm 𝕜 𝕜 H)

/-- Every-hyperplane isomorphism implies scalar absorption whenever the
space is nonzero; Hahn--Banach supplies a genuine nonzero functional. -/
theorem IsIsomorphicToEveryHyperplane.scalarExtension [Nontrivial X]
    (h : IsIsomorphicToEveryHyperplane 𝕜 X) : IsIsomorphicToScalarExtension 𝕜 X := by
  obtain ⟨f, hf, _⟩ := exists_dual_vector' 𝕜 (0 : X)
  have hf0 : f ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hf
    exact zero_ne_one hf
  have hH := scalarFunctional_closedHyperplane f hf0
  obtain ⟨a⟩ := h (LinearMap.ker f.toLinearMap) hH
  exact ⟨(closedHyperplaneProductEquiv _ hH).trans
    (a.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))⟩

/-- A Banach space of order one sits as a genuine hyperplane in its bidual. -/
theorem IsQuasiReflexiveOfOrderOne.bidualHyperplane [CompleteSpace X]
    (h : IsQuasiReflexiveOfOrderOne 𝕜 X) :
    IsClosedHyperplane 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) (bidualImage 𝕜 X) :=
  ⟨isClosed_bidualImage, h⟩

/-- The canonical bidual copy is isometric to the original normed space. -/
def canonicalBidualImageEquiv : X ≃L[𝕜] bidualImage 𝕜 X :=
  (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := X)).equivRange.toContinuousLinearEquiv

/-- The actual bidual of an order-one Banach space is isomorphic to X × 𝕜. -/
def IsQuasiReflexiveOfOrderOne.bidualScalarEquiv [CompleteSpace X]
    (h : IsQuasiReflexiveOfOrderOne 𝕜 X) :
    StrongDual 𝕜 (StrongDual 𝕜 X) ≃L[𝕜] (X × 𝕜) :=
  (closedHyperplaneProductEquiv (𝕜 := 𝕜) (bidualImage 𝕜 X) h.bidualHyperplane).trans
    ((canonicalBidualImageEquiv (𝕜 := 𝕜) (X := X)).symm.prodCongr
      (ContinuousLinearEquiv.refl 𝕜 𝕜))

theorem IsQuasiReflexiveOfOrderOne.nontrivial
    (h : IsQuasiReflexiveOfOrderOne 𝕜 X) : Nontrivial X := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · letI : Subsingleton (StrongDual 𝕜 X) := ⟨fun f g => ContinuousLinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    letI : Subsingleton (StrongDual 𝕜 (StrongDual 𝕜 X)) :=
      ⟨fun f g => ContinuousLinearMap.ext fun x => by
        rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    letI : Subsingleton (ResiduumSpace 𝕜 X) :=
      (bidualImage 𝕜 X).mkQ_surjective.subsingleton
    have hr : Module.rank 𝕜 (ResiduumSpace 𝕜 X) = 0 := rank_subsingleton' _ _
    exact False.elim (zero_ne_one (hr.symm.trans h))
  · exact hX

/-- The hypotheses of B.3 give a concrete bounded isomorphism X** ≃ X. -/
def IsQuasiReflexiveOfOrderOne.bidualSelfEquiv [CompleteSpace X]
    (h : IsQuasiReflexiveOfOrderOne 𝕜 X)
    (hh : IsIsomorphicToEveryHyperplane 𝕜 X) :
    StrongDual 𝕜 (StrongDual 𝕜 X) ≃L[𝕜] X := by
  letI := h.nontrivial
  let e := Classical.choice hh.scalarExtension
  exact h.bidualScalarEquiv.trans e.symm

end ThesisCommon
