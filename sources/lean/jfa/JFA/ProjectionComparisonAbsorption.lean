import JFA.ProjectionComparisonKernel

/-! A space containing complemented c₀ absorbs any complemented retract of
c₀. The comparison kernel therefore disappears from the actual range/kernel
splitting, identifying the two projection ranges without countable
self-similarity of either range. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E X Z : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem absorbs_cZero_retract (UX : cZero 𝕜 →L[𝕜] X) (VX : X →L[𝕜] cZero 𝕜)
    (hX : VX.comp UX = ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    (AZ : Z →L[𝕜] cZero 𝕜) (BZ : cZero 𝕜 →L[𝕜] Z)
    (hZ : BZ.comp AZ = ContinuousLinearMap.id 𝕜 Z) : Isomorphic 𝕜 (X × Z) X := by
  obtain ⟨W, hW, ⟨e⟩⟩ := projection_factorization_complemented
    (ContinuousLinearMap.id 𝕜 Z) (by simp) AZ BZ hZ
  let eId := (LinearIsometryEquiv.ofTop Z
    (LinearMap.range (ContinuousLinearMap.id 𝕜 Z).toLinearMap) LinearMap.range_id).toContinuousLinearEquiv.symm
  obtain ⟨f⟩ := absorbs_complemented_cZero_subspace UX VX hX W hW
  exact ⟨((ContinuousLinearEquiv.refl 𝕜 X).prodCongr (eId.trans e)).trans f⟩

theorem projection_ranges_isomorphic_of_cZero_difference (P Q : E →L[𝕜] E)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (A : E →L[𝕜] cZero 𝕜) (B : cZero 𝕜 →L[𝕜] E) (hBA : B.comp A = P - Q)
    (UP : cZero 𝕜 →L[𝕜] LinearMap.range P.toLinearMap)
    (VP : LinearMap.range P.toLinearMap →L[𝕜] cZero 𝕜)
    (hVP : VP.comp UP = ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    (UQ : cZero 𝕜 →L[𝕜] LinearMap.range Q.toLinearMap)
    (VQ : LinearMap.range Q.toLinearMap →L[𝕜] cZero 𝕜)
    (hVQ : VQ.comp UQ = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (LinearMap.range Q.toLinearMap) := by
  obtain ⟨F, G, hGF, U, V, hVU⟩ := projection_range_comparison_kernel_retract P Q hP hQ A B hBA
  obtain ⟨eAbsP⟩ := absorbs_cZero_retract UP VP hVP U V hVU
  obtain ⟨eAbsQ⟩ := absorbs_cZero_of_retract UQ VQ hVQ
  let eSplit := ContinuousLinearEquiv.equivOfRightInverse G F
    (fun z => congrArg (fun L => L z) hGF)
  exact ⟨(eAbsQ.symm.trans (eSplit.trans eAbsP)).symm⟩

end JFA
