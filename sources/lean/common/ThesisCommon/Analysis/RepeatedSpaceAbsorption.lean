import ThesisCommon.Analysis.PelczynskiDecomposition

/-! Absorbing a repeated ambient space absorbs each of its actual bounded
retracts. No self-similarity assumption on the absorbed retract is needed. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

def absorbComplementedOfRepeatedAbsorption (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (eX : X ≃L[𝕜] X × lp (fun _ : ℕ => Y) p)
    (J : Z →L[𝕜] Y) (Q : Y →L[𝕜] Z)
    (hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 Z) : X ≃L[𝕜] X × Z := by
  let eY : Y ≃L[𝕜] Z × LinearMap.ker Q.toLinearMap :=
    ContinuousLinearEquiv.equivOfRightInverse Q J (fun z => DFunLike.congr_fun hQJ z)
  let eSum := (lpMapEquiv (ι := ℕ) p eY).trans (lpProdEquiv p)
  let eStable := eX.trans ((ContinuousLinearEquiv.refl 𝕜 X).prodCongr eSum)
  exact (absorbProductEquiv eStable (lpHeadTailEquiv p)).symm

end ThesisCommon
