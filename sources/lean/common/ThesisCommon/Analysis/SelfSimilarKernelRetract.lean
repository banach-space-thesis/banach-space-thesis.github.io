import ThesisCommon.Analysis.PrimaryMutualRetracts
import ThesisCommon.Analysis.SequenceCoordinates

/-! A countably self-similar space embeds complementably in the kernel of
any continuous scalar functional. This elementary two-coordinate argument
avoids a hyperplane cancellation assumption. -/

noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem selfSimilar_kernel_retract (p : BanachExponent)
    (e : X ≃L[𝕜] SequenceSum p X) (f : X →L[𝕜] 𝕜) :
    ∃ A : LinearMap.ker f.toLinearMap →L[𝕜] X,
      ∃ B : X →L[𝕜] LinearMap.ker f.toLinearMap,
        A.comp B = ContinuousLinearMap.id 𝕜 X := by
  classical
  let V (i : ℕ) : X →L[𝕜] X :=
    e.symm.toContinuousLinearMap.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p.val i)
  let U (i : ℕ) : X →L[𝕜] X := (lpCoordinate p.val i).comp e.toContinuousLinearMap
  have hUV (i j : ℕ) (x : X) : U i (V j x) = if i = j then x else 0 := by
    change (e (e.symm (lp.single p.val j x))) i = _
    rw [e.apply_symm_apply]
    by_cases hij : i = j
    · subst j; simp
    · simp [lp.single_apply_ne, hij]
  let H := LinearMap.ker f.toLinearMap
  by_cases hzero : f.comp (V 1) = 0
  · let B : X →L[𝕜] H := (V 1).codRestrict H (fun x => by
      have hx := congrArg (fun F : X →L[𝕜] 𝕜 => F x) hzero
      exact hx)
    refine ⟨(U 1).comp H.subtypeL, B, ?_⟩
    ext x
    exact (hUV 1 1 x).trans (if_pos rfl)
  · have hex : ∃ y : X, f (V 1 y) ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hzero (ContinuousLinearMap.ext hn)
    obtain ⟨y, hy⟩ := hex
    let z : X := (f (V 1 y))⁻¹ • V 1 y
    have hfz : f z = 1 := by simp [z, hy]
    have hUz : U 0 z = 0 := by simp [z, hUV]
    let W : X →L[𝕜] X := V 0 - (f.comp (V 0)).smulRight z
    let B : X →L[𝕜] H := W.codRestrict H (fun x => by
      change f (V 0 x - f (V 0 x) • z) = 0
      simp [hfz])
    refine ⟨(U 0).comp H.subtypeL, B, ?_⟩
    ext x
    change U 0 (V 0 x - f (V 0 x) • z) = x
    simp [hUV, hUz]

end ThesisCommon
