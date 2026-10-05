import JFA.CZeroAbsorption

/-! Projections whose difference factors through c₀ have complemented range
embeddings after adding c₀. When one range is its own countable C₀ sum and
both ranges contain complemented c₀, the decomposition method identifies them.
No conjugation of a projection with a nonzero kernel to the identity is used. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem absorbs_cZero_of_retract (U : cZero 𝕜 →L[𝕜] X) (V : X →L[𝕜] cZero 𝕜)
    (hVU : V.comp U = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :
    Isomorphic 𝕜 (X × cZero 𝕜) X := by
  have htop : IsComplemented 𝕜 (cZero 𝕜) (⊤ : Submodule 𝕜 (cZero 𝕜)) := by
    refine ⟨ContinuousLinearMap.id 𝕜 _, by simp, ?_⟩
    exact LinearMap.range_id
  obtain ⟨f⟩ := absorbs_complemented_cZero_subspace U V hVU _ htop
  exact ⟨((ContinuousLinearEquiv.refl 𝕜 X).prodCongr
    (LinearIsometryEquiv.ofTop (cZero 𝕜) (⊤ : Submodule 𝕜 (cZero 𝕜)) rfl).toContinuousLinearEquiv.symm).trans f⟩

theorem projection_range_stabilized_retract (P Q : E →L[𝕜] E)
    (hP : P.comp P = P) (A : E →L[𝕜] cZero 𝕜) (B : cZero 𝕜 →L[𝕜] E)
    (hBA : B.comp A = P - Q) :
    ∃ F : LinearMap.range P.toLinearMap →L[𝕜] (LinearMap.range Q.toLinearMap × cZero 𝕜),
    ∃ G : (LinearMap.range Q.toLinearMap × cZero 𝕜) →L[𝕜] LinearMap.range P.toLinearMap,
      G.comp F = ContinuousLinearMap.id 𝕜 (LinearMap.range P.toLinearMap) := by
  let F := (Q.rangeRestrict.comp (LinearMap.range P.toLinearMap).subtypeL).prod
    (A.comp (LinearMap.range P.toLinearMap).subtypeL)
  let G := P.rangeRestrict.comp ((LinearMap.range Q.toLinearMap).subtypeL.coprod B)
  refine ⟨F, G, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  apply Subtype.ext
  change P (Q z.val + B (A z.val)) = z.val
  have hz : B (A z.val) = P z.val - Q z.val := congrArg (fun L => L z.val) hBA
  have heq : Q z.val + B (A z.val) = P z.val := by rw [hz]; abel
  rw [heq, projection_fix_range P hP z, projection_fix_range P hP z]

theorem isomorphic_of_stabilized_cZero_retracts
    (eX : X ≃L[𝕜] C₀(ℕ, X))
    (eAbsX : (X × cZero 𝕜) ≃L[𝕜] X) (eAbsY : (Y × cZero 𝕜) ≃L[𝕜] Y)
    (FX : X →L[𝕜] (Y × cZero 𝕜)) (GX : (Y × cZero 𝕜) →L[𝕜] X)
    (hGX : GX.comp FX = ContinuousLinearMap.id 𝕜 X)
    (FY : Y →L[𝕜] (X × cZero 𝕜)) (GY : (X × cZero 𝕜) →L[𝕜] Y)
    (hGY : GY.comp FY = ContinuousLinearMap.id 𝕜 Y) : Isomorphic 𝕜 Y X := by
  let UX := eAbsY.toContinuousLinearMap.comp FX
  let VX := GX.comp eAbsY.symm.toContinuousLinearMap
  let UY := eAbsX.toContinuousLinearMap.comp FY
  let VY := GY.comp eAbsX.symm.toContinuousLinearMap
  have hVX (x : X) : VX (UX x) = x := by
    simp only [VX, UX, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    exact congrArg (fun L => L x) hGX
  have hVY (y : Y) : VY (UY y) = y := by
    simp only [VY, UY, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    exact congrArg (fun L => L y) hGY
  exact ⟨(ThesisCommon.cZeroDecompositionEquiv eX
    (ContinuousLinearEquiv.equivOfRightInverse VY UY hVY)
    (ContinuousLinearEquiv.equivOfRightInverse VX UX hVX)).symm⟩

theorem projection_range_iso_of_cZero_difference (P Q : E →L[𝕜] E)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (A : E →L[𝕜] cZero 𝕜) (B : cZero 𝕜 →L[𝕜] E) (hBA : B.comp A = P - Q)
    (eQ : LinearMap.range Q.toLinearMap ≃L[𝕜] C₀(ℕ, LinearMap.range Q.toLinearMap))
    (UP : cZero 𝕜 →L[𝕜] LinearMap.range P.toLinearMap)
    (VP : LinearMap.range P.toLinearMap →L[𝕜] cZero 𝕜)
    (hVP : VP.comp UP = ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    (UQ : cZero 𝕜 →L[𝕜] LinearMap.range Q.toLinearMap)
    (VQ : LinearMap.range Q.toLinearMap →L[𝕜] cZero 𝕜)
    (hVQ : VQ.comp UQ = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (LinearMap.range Q.toLinearMap) := by
  obtain ⟨FP, GP, hGP⟩ := projection_range_stabilized_retract P Q hP A B hBA
  have hABneg : (-B).comp A = Q - P := by
    rw [ContinuousLinearMap.neg_comp, hBA]
    abel
  obtain ⟨FQ, GQ, hGQ⟩ := projection_range_stabilized_retract Q P hQ A (-B) hABneg
  obtain ⟨eAbsP⟩ := absorbs_cZero_of_retract UP VP hVP
  obtain ⟨eAbsQ⟩ := absorbs_cZero_of_retract UQ VQ hVQ
  exact isomorphic_of_stabilized_cZero_retracts eQ eAbsQ eAbsP FQ GQ hGQ FP GP hGP

end JFA
