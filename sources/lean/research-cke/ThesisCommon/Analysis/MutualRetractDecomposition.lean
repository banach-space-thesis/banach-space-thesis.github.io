import ThesisCommon.Analysis.PelczynskiDecomposition

/-! Pełczyński decomposition packaged directly for two pairs of retraction
operators. The complement spaces are their actual kernels. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem equiv_of_cZero_selfSimilar_mutual_retracts
    (e : X ≃L[𝕜] CZeroSum X)
    (P : X →L[𝕜] Y) (J : Y →L[𝕜] X)
    (Q : Y →L[𝕜] X) (I : X →L[𝕜] Y)
    (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 Y)
    (hQI : Q.comp I = ContinuousLinearMap.id 𝕜 X) :
    Nonempty (Y ≃L[𝕜] X) := by
  let eXY : X ≃L[𝕜] Y × LinearMap.ker P.toLinearMap :=
    ContinuousLinearEquiv.equivOfRightInverse P J
      (fun y => DFunLike.congr_fun hPJ y)
  let eYX : Y ≃L[𝕜] X × LinearMap.ker Q.toLinearMap :=
    ContinuousLinearEquiv.equivOfRightInverse Q I
      (fun x => DFunLike.congr_fun hQI x)
  exact ⟨(cZeroDecompositionEquiv (𝕜 := 𝕜) (X := X) (Y := Y)
    (A := LinearMap.ker Q.toLinearMap) (B := LinearMap.ker P.toLinearMap)
    e eXY eYX).symm⟩

end ThesisCommon
