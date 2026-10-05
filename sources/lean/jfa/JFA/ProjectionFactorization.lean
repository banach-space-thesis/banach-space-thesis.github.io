import JFA.Definitions

/-! A bounded projection factoring through F has range isomorphic to a
complemented subspace of F. The complementary projection and both inverse
bounded maps are constructed explicitly. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem projection_fix_range (P : E →L[𝕜] E) (hP : P.comp P = P)
    (z : LinearMap.range P.toLinearMap) : P z.val = z.val := by
  obtain ⟨x, hx⟩ := z.property
  rw [← hx]
  exact congrArg (fun T : E →L[𝕜] E => T x) hP

theorem projection_factorization_complemented (P : E →L[𝕜] E) (hP : P.comp P = P)
    (A : E →L[𝕜] F) (B : F →L[𝕜] E) (hBA : B.comp A = P) :
    ∃ W : Submodule 𝕜 F, IsComplemented 𝕜 F W ∧
      Isomorphic 𝕜 (LinearMap.range P.toLinearMap) W := by
  let Q : F →L[𝕜] F := A.comp (P.comp B)
  have hPx (x : E) : P (P x) = P x := congrArg (fun T : E →L[𝕜] E => T x) hP
  have hBAx (x : E) : B (A x) = P x := congrArg (fun T : E →L[𝕜] E => T x) hBA
  have hQ : Q.comp Q = Q := by
    apply ContinuousLinearMap.ext
    intro f
    change A (P (B (A (P (B f))))) = A (P (B f))
    rw [hBAx, hPx, hPx]
  let α : LinearMap.range P.toLinearMap →L[𝕜] F := A.comp (LinearMap.range P.toLinearMap).subtypeL
  let β : F →L[𝕜] LinearMap.range P.toLinearMap :=
    (P.codRestrict (LinearMap.range P.toLinearMap) (fun x => ⟨x, rfl⟩)).comp B
  let α' : LinearMap.range P.toLinearMap →L[𝕜] LinearMap.range Q.toLinearMap :=
    α.codRestrict (LinearMap.range Q.toLinearMap) (fun z => ⟨A z.val, by
      change A (P (B (A z.val))) = A z.val
      rw [hBAx, hPx, projection_fix_range P hP z]⟩)
  let β' : LinearMap.range Q.toLinearMap →L[𝕜] LinearMap.range P.toLinearMap :=
    β.comp (LinearMap.range Q.toLinearMap).subtypeL
  have hαβ : α'.comp β' = ContinuousLinearMap.id 𝕜 (LinearMap.range Q.toLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change Q z.val = z.val
    exact projection_fix_range Q hQ z
  have hβα : β'.comp α' = ContinuousLinearMap.id 𝕜 (LinearMap.range P.toLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change P (B (A z.val)) = z.val
    rw [hBAx, hPx, projection_fix_range P hP z]
  exact ⟨LinearMap.range Q.toLinearMap, ⟨Q, hQ, rfl⟩,
    ⟨ContinuousLinearEquiv.equivOfInverse' α' β' hαβ hβα⟩⟩

end JFA
