import ThesisCommon.Analysis.ProjectionDecomposition

/-! When a factorization through a projection reads via an invertible map
after a prescribed sampling map, the remaining summand is complementably
embedded in that sampling kernel. Every map is constructed explicitly. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem projection_range_sampling_decomposition
    (P S V : X →L[𝕜] X) (hP : P.comp P = P) (E : X ≃L[𝕜] X)
    (hf : (E.toContinuousLinearMap.comp S).comp (P.comp V) = ContinuousLinearMap.id 𝕜 X) :
    ∃ R : LinearMap.range P.toLinearMap →L[𝕜] X,
      Nonempty (LinearMap.range P.toLinearMap ≃L[𝕜] X × LinearMap.ker R.toLinearMap) ∧
      ∃ (J : LinearMap.ker R.toLinearMap →L[𝕜] LinearMap.ker S.toLinearMap)
        (Q : LinearMap.ker S.toLinearMap →L[𝕜] LinearMap.ker R.toLinearMap),
        Q.comp J = ContinuousLinearMap.id 𝕜 _ := by
  let R : LinearMap.range P.toLinearMap →L[𝕜] X :=
    S.comp (LinearMap.range P.toLinearMap).subtypeL
  let B : X →L[𝕜] LinearMap.range P.toLinearMap :=
    (P.rangeRestrict.comp V).comp E.toContinuousLinearMap
  have hRB (x : X) : R (B x) = x := by
    apply E.injective
    exact DFunLike.congr_fun hf (E x)
  let π : LinearMap.range P.toLinearMap →L[𝕜] LinearMap.ker R.toLinearMap :=
    (ContinuousLinearMap.id 𝕜 _ - B.comp R).codRestrict _ (by
      intro y
      change R (y - B (R y)) = 0
      rw [map_sub, hRB, sub_self])
  let J : LinearMap.ker R.toLinearMap →L[𝕜] LinearMap.ker S.toLinearMap :=
    ((LinearMap.range P.toLinearMap).subtypeL.comp
      (LinearMap.ker R.toLinearMap).subtypeL).codRestrict _ (fun z => z.property)
  let Q : LinearMap.ker S.toLinearMap →L[𝕜] LinearMap.ker R.toLinearMap :=
    (π.comp P.rangeRestrict).comp (LinearMap.ker S.toLinearMap).subtypeL
  refine ⟨R, ⟨ContinuousLinearEquiv.equivOfRightInverse R B hRB⟩, J, Q, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  have hPz : P z.val.val = z.val.val := by
    obtain ⟨x, hx⟩ := z.val.property
    rw [← hx]
    exact DFunLike.congr_fun hP x
  have hRz : R z.val = 0 := z.property
  have hPz' : P.rangeRestrict z.val.val = z.val := Subtype.ext hPz
  change π (P.rangeRestrict z.val.val) = z
  rw [hPz']
  apply Subtype.ext
  change z.val - B (R z.val) = z.val
  rw [hRz, map_zero, sub_zero]

end ThesisCommon
