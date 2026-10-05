import JFA.InjectiveFunctor
import JFA.ProjectionFactorization

/-! Tensoring a bounded projection gives a projection whose range is the
injective tensor product of the original range. Bounded linear equivalences
also induce actual equivalences of the concrete tensor completions. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def injectiveTensorEquiv (e : E ≃L[𝕜] F) :
    InjectiveTensor 𝕜 E X ≃L[𝕜] InjectiveTensor 𝕜 F X := by
  have hVU : e.symm.toContinuousLinearMap.comp e.toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 E := by ext z; exact e.symm_apply_apply z
  have hUV : e.toContinuousLinearMap.comp e.symm.toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 F := by ext z; exact e.apply_symm_apply z
  apply ContinuousLinearEquiv.equivOfInverse' (injectiveTensorMap e.toContinuousLinearMap)
    (injectiveTensorMap e.symm.toContinuousLinearMap)
  · rw [← injectiveTensorMap_comp, hUV, injectiveTensorMap_id]
  · rw [← injectiveTensorMap_comp, hVU, injectiveTensorMap_id]

theorem injectiveTensorMap_projection (P : E →L[𝕜] E) (hP : P.comp P = P) :
    (injectiveTensorMap (X := X) P).comp (injectiveTensorMap P) = injectiveTensorMap P := by
  rw [← injectiveTensorMap_comp, hP]

def injectiveTensorProjectionRangeEquiv (P : E →L[𝕜] E) (hP : P.comp P = P) :
    LinearMap.range (injectiveTensorMap (X := X) P).toLinearMap ≃L[𝕜]
      InjectiveTensor 𝕜 (LinearMap.range P.toLinearMap) X := by
  let R := P.rangeRestrict
  let J := (LinearMap.range P.toLinearMap).subtypeL
  have hRJ : R.comp J = ContinuousLinearMap.id 𝕜 (LinearMap.range P.toLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    exact Subtype.ext (projection_fix_range P hP z)
  have hJR : J.comp R = P := by ext z; rfl
  have hPJ : P.comp J = J := by ext z; exact projection_fix_range P hP z
  let TP := injectiveTensorMap (X := X) P
  let TR := injectiveTensorMap (X := X) R
  let TJ := injectiveTensorMap (X := X) J
  have hTRJ : TR.comp TJ = ContinuousLinearMap.id 𝕜
      (InjectiveTensor 𝕜 (LinearMap.range P.toLinearMap) X) := by
    rw [← injectiveTensorMap_comp, hRJ, injectiveTensorMap_id]
  have hTJR : TJ.comp TR = TP := by rw [← injectiveTensorMap_comp, hJR]
  have hTPJ : TP.comp TJ = TJ := by rw [← injectiveTensorMap_comp, hPJ]
  let TJ' := TJ.codRestrict (LinearMap.range TP.toLinearMap) (fun z =>
    ⟨TJ z, congrArg (fun L => L z) hTPJ⟩)
  let TR' := TR.comp (LinearMap.range TP.toLinearMap).subtypeL
  apply ContinuousLinearEquiv.equivOfInverse' TR' TJ'
  · apply ContinuousLinearMap.ext
    intro z
    exact congrArg (fun L => L z) hTRJ
  · apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    have hz := congrArg (fun L => L z.val) hTJR
    exact hz.trans (projection_fix_range TP (injectiveTensorMap_projection P hP) z)

def conjugateProjectionRangeEquiv (c : E ≃L[𝕜] F) (P : E →L[𝕜] E)
    (Q : F →L[𝕜] F) (hQ : Q = c.toContinuousLinearMap.comp
      (P.comp c.symm.toContinuousLinearMap)) :
    LinearMap.range P.toLinearMap ≃L[𝕜] LinearMap.range Q.toLinearMap := by
  have hc (x : E) : Q (c x) = c (P x) := by
    rw [hQ]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  have hd (y : F) : P (c.symm y) = c.symm (Q y) := by
    rw [hQ]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  let A := (c.toContinuousLinearMap.comp (LinearMap.range P.toLinearMap).subtypeL).codRestrict
    (LinearMap.range Q.toLinearMap) (fun z => by
      obtain ⟨x, hx⟩ := z.property
      exact ⟨c x, (hc x).trans (congrArg c hx)⟩)
  let B := (c.symm.toContinuousLinearMap.comp (LinearMap.range Q.toLinearMap).subtypeL).codRestrict
    (LinearMap.range P.toLinearMap) (fun z => by
      obtain ⟨y, hy⟩ := z.property
      exact ⟨c.symm y, (hd y).trans (congrArg c.symm hy)⟩)
  apply ContinuousLinearEquiv.equivOfInverse A B
  · intro z
    exact Subtype.ext (c.symm_apply_apply z.val)
  · intro z
    exact Subtype.ext (c.apply_symm_apply z.val)

end JFA
