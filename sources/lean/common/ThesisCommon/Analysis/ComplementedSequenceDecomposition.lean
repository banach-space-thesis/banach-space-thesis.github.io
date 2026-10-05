import ThesisCommon.Analysis.PelczynskiDecomposition
import ThesisCommon.Analysis.InfinitySelfSimilarity

/-! The checked decomposition method applied directly to complementary
embeddings, keeping all complementary spaces as actual bounded-map kernels. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def lpDecompositionEquivOfRetractions (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (eX : X ≃L[𝕜] lp (fun _ : ℕ => X) p)
    (J : Y →L[𝕜] X) (Q : X →L[𝕜] Y) (hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 Y)
    (I : X →L[𝕜] Y) (R : Y →L[𝕜] X) (hRI : R.comp I = ContinuousLinearMap.id 𝕜 X) :
    X ≃L[𝕜] Y :=
  lpDecompositionEquiv p eX
    (ContinuousLinearEquiv.equivOfRightInverse Q J (fun x => DFunLike.congr_fun hQJ x))
    (ContinuousLinearEquiv.equivOfRightInverse R I (fun x => DFunLike.congr_fun hRI x))

def infinitySequenceEquivOfRetraction
    (J : lp (fun _ : ℕ => X) ∞ →L[𝕜] X)
    (Q : X →L[𝕜] lp (fun _ : ℕ => X) ∞)
    (hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => X) ∞)) :
    X ≃L[𝕜] lp (fun _ : ℕ => X) ∞ :=
  (lpDecompositionEquivOfRetractions ∞ infinityFlattenEquiv.symm
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ 0)
    (lpCoordinate ∞ 0) (by
      apply ContinuousLinearMap.ext
      intro x
      change (lp.single ∞ 0 x : lp (fun _ : ℕ => X) ∞) 0 = x
      rw [lp.single_apply_self]) J Q hQJ).symm

end ThesisCommon
