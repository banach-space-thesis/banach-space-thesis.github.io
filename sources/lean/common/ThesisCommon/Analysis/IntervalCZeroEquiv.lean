import ThesisCommon.Analysis.IntervalCZeroRetraction
import ThesisCommon.Analysis.PelczynskiDecomposition
import ThesisCommon.Analysis.CZeroSelfSimilarity

/-! A constructive proof of C[0,1] ≃ c0(C[0,1]). Disjoint tapered
windows give the complemented copy in C[0,1], the head coordinate gives
the reverse complemented embedding, and Pełczyński decomposition finishes.
No classification theorem or isomorphism assumption is used. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def intervalCZeroProductEquiv : IntervalContinuous 𝕜 ≃L[𝕜]
    CZeroSum (IntervalContinuous 𝕜) × LinearMap.ker (intervalCZeroRead (𝕜 := 𝕜)).toLinearMap :=
  ContinuousLinearEquiv.equivOfRightInverse (intervalCZeroRead (𝕜 := 𝕜)) (intervalCZeroInsert (𝕜 := 𝕜))
    (fun x => DFunLike.congr_fun (intervalCZeroRead_comp_insert (𝕜 := 𝕜)) x)

def cZeroEquivOfRetraction {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (P : Y →L[𝕜] CZeroSum Y) (J : CZeroSum Y →L[𝕜] Y)
    (h : ∀ x, P (J x) = x) : Y ≃L[𝕜] CZeroSum Y :=
  (cZeroDecompositionEquiv (𝕜 := 𝕜) (X := CZeroSum Y)
    (Y := Y) (B := CZeroSum Y) (A := LinearMap.ker P.toLinearMap)
    (cZeroFlattenEquiv (𝕜 := 𝕜) (X := Y)).symm
    (cZeroHeadTailEquiv (𝕜 := 𝕜) (X := Y))
    (ContinuousLinearEquiv.equivOfRightInverse P J h)).symm

def intervalCZeroEquiv : IntervalContinuous 𝕜 ≃L[𝕜] CZeroSum (IntervalContinuous 𝕜) :=
  cZeroEquivOfRetraction (intervalCZeroRead (𝕜 := 𝕜)) (intervalCZeroInsert (𝕜 := 𝕜))
    (fun x => DFunLike.congr_fun (intervalCZeroRead_comp_insert (𝕜 := 𝕜)) x)

theorem interval_sequenceSelfSimilar : IsSequenceSelfSimilar 𝕜 (IntervalContinuous 𝕜) :=
  Or.inr ⟨intervalCZeroEquiv⟩

end ThesisCommon
