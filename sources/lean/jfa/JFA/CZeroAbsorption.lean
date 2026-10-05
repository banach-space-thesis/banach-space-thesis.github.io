import JFA.CZeroComplementedSubspaces

/-! Scalar c₀ absorbs each of its complemented subspaces. Consequently a
space containing a complemented c₀ copy absorbs each such subspace too.
These equivalences keep the actual kernel complements in the decomposition. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]

def cZeroSquareEquiv : cZero 𝕜 ≃L[𝕜] cZero 𝕜 × cZero 𝕜 :=
  (ThesisCommon.cZeroFlattenEquiv (𝕜 := 𝕜) (X := 𝕜)).symm.trans
    ((ThesisCommon.cZeroHeadTailEquiv (𝕜 := 𝕜) (X := cZero 𝕜)).trans
      ((ContinuousLinearEquiv.refl 𝕜 (cZero 𝕜)).prodCongr
        (ThesisCommon.cZeroFlattenEquiv (𝕜 := 𝕜) (X := 𝕜))))

theorem cZero_absorbs_complemented (W : Submodule 𝕜 (cZero 𝕜))
    (hW : IsComplemented 𝕜 (cZero 𝕜) W) :
    Isomorphic 𝕜 (cZero 𝕜 × W) (cZero 𝕜) := by
  obtain ⟨P, hP, hPW⟩ := hW
  rw [← hPW]
  let eXY := (cZeroSquareEquiv (𝕜 := 𝕜)).trans
    (((ContinuousLinearEquiv.refl 𝕜 (cZero 𝕜)).prodCongr
      (ThesisCommon.projectionRangeKerEquiv P hP)).trans
        (ContinuousLinearEquiv.prodAssoc 𝕜 _ _ _).symm)
  exact ⟨(ThesisCommon.cZeroDecompositionEquiv
    (ThesisCommon.cZeroFlattenEquiv (𝕜 := 𝕜) (X := 𝕜)).symm eXY
    (ContinuousLinearEquiv.refl 𝕜 (cZero 𝕜 × LinearMap.range P.toLinearMap))).symm⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem absorbs_complemented_cZero_subspace
    (A : cZero 𝕜 →L[𝕜] E) (B : E →L[𝕜] cZero 𝕜)
    (hBA : B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    (W : Submodule 𝕜 (cZero 𝕜)) (hW : IsComplemented 𝕜 (cZero 𝕜) W) :
    Isomorphic 𝕜 (E × W) E := by
  let e := ContinuousLinearEquiv.equivOfRightInverse B A (fun x =>
    congrArg (fun L => L x) hBA)
  obtain ⟨f⟩ := cZero_absorbs_complemented W hW
  exact ⟨(e.prodCongr (ContinuousLinearEquiv.refl 𝕜 W)).trans
    ((ContinuousLinearEquiv.prodAssoc 𝕜 _ _ _).trans
      (((ContinuousLinearEquiv.refl 𝕜 (cZero 𝕜)).prodCongr
        (ContinuousLinearEquiv.prodComm 𝕜 _ _)).trans
          ((ContinuousLinearEquiv.prodAssoc 𝕜 _ _ _).symm.trans
            ((f.prodCongr (ContinuousLinearEquiv.refl 𝕜 _)).trans e.symm))))⟩

theorem projection_complement_range_eq_kernel (P : E →L[𝕜] E) (hP : P.comp P = P) :
    LinearMap.range (ContinuousLinearMap.id 𝕜 E - P).toLinearMap =
      LinearMap.ker P.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change P (y - P y) = 0
    have hy : P (P y) = P y := congrArg (fun L => L y) hP
    rw [map_sub, hy, sub_self]
  · intro hx
    refine ⟨x, ?_⟩
    change P x = 0 at hx
    change x - P x = x
    rw [hx, sub_zero]

theorem projection_range_iso_of_complement_factors_cZero
    (P : E →L[𝕜] E) (hP : P.comp P = P)
    (A : E →L[𝕜] cZero 𝕜) (B : cZero 𝕜 →L[𝕜] E)
    (hAB : B.comp A = ContinuousLinearMap.id 𝕜 E - P)
    (U : cZero 𝕜 →L[𝕜] LinearMap.range P.toLinearMap)
    (V : LinearMap.range P.toLinearMap →L[𝕜] cZero 𝕜)
    (hVU : V.comp U = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) E := by
  let Q := ContinuousLinearMap.id 𝕜 E - P
  have hQ : Q.comp Q = Q := ThesisCommon.complementary_projection hP
  obtain ⟨W, hW, ⟨eQ⟩⟩ := projection_factorization_complemented Q hQ A B hAB
  have hKQ : LinearMap.ker P.toLinearMap = LinearMap.range Q.toLinearMap :=
    (projection_complement_range_eq_kernel P hP).symm
  let eKQ : LinearMap.ker P.toLinearMap ≃L[𝕜] LinearMap.range Q.toLinearMap :=
    (LinearIsometryEquiv.ofEq _ _ hKQ).toContinuousLinearEquiv
  obtain ⟨f⟩ := absorbs_complemented_cZero_subspace U V hVU W hW
  exact ⟨((ThesisCommon.projectionRangeKerEquiv P hP).trans
    (((ContinuousLinearEquiv.refl 𝕜 (LinearMap.range P.toLinearMap)).prodCongr
      (eKQ.trans eQ)).trans f)).symm⟩

end JFA
