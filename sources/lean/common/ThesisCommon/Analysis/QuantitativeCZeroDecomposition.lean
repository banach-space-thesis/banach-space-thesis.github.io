import ThesisCommon.Analysis.BoundedCZeroEquivalenceCalculus
import ThesisCommon.Analysis.QuantitativeSequenceDecomposition

/-! The c₀ counterpart of the coarse quantitative sequence decomposition,
on actual null-sequence spaces and with the same polynomial estimate. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y A B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]

theorem cZeroDecompositionEquiv_normBound
    (eX : X ≃L[𝕜] CZeroSum X)
    (eXY : X ≃L[𝕜] Y × B) (eYX : Y ≃L[𝕜] X × A)
    {D : ℝ} (hD : 1 ≤ D) (hX : EquivNormBound eX 1)
    (hXY : EquivNormBound eXY D) (hYX : EquivNormBound eYX D) :
    EquivNormBound (cZeroDecompositionEquiv eX eXY eYX) (32 * D ^ 5) := by
  have hD0 := zero_le_one.trans hD
  have hD2 : 1 ≤ D * D := by nlinarith
  let e := eXY.trans (eYX.prodCongr (ContinuousLinearEquiv.refl 𝕜 B))
  have he : EquivNormBound e (D * D) :=
    hXY.trans (hYX.prodCongr (equivNormBound_refl |>.mono hD) hD0) hD0 hD0
  let eSum := (cZeroMapEquiv (ι := ℕ) e).trans
    (cZeroProdEquiv.trans
      ((cZeroProdEquiv.prodCongr
        (ContinuousLinearEquiv.refl 𝕜 (CZeroSum B))).trans
          (ContinuousLinearEquiv.prodAssoc 𝕜 _ _ _)))
  have h₂ := (equivNormBound_cZeroProd (𝕜 := 𝕜) (X := X) (Y := A)).prodCongr
    (equivNormBound_refl (𝕜 := 𝕜) (X := CZeroSum B) |>.mono (by norm_num))
    (by norm_num : (0 : ℝ) ≤ 2)
  have h₃ := h₂.trans (equivNormBound_assoc (𝕜 := 𝕜)) (by norm_num) zero_le_one
  have h₄ := (equivNormBound_cZeroProd (𝕜 := 𝕜) (X := X × A) (Y := B)).trans
    h₃ (by norm_num) (by norm_num)
  have hSum : EquivNormBound eSum (4 * D ^ 2) := by
    have h := (he.cZeroMap (mul_nonneg hD0 hD0)).trans h₄
      (mul_nonneg hD0 hD0) (by norm_num)
    change EquivNormBound eSum ((D * D) * (2 * (2 * 1))) at h
    convert h using 1; ring
  let eStable := (eX.trans eSum).trans
    (eX.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 _))
  have hS0 : 0 ≤ 4 * D ^ 2 := by positivity
  have hS1 : 1 ≤ 4 * D ^ 2 := by nlinarith
  have hStable : EquivNormBound eStable (4 * D ^ 2) := by
    have h := (hX.trans hSum zero_le_one hS0).trans
      (hX.symm.prodCongr equivNormBound_refl zero_le_one)
      (by simpa only [one_mul] using hS0) zero_le_one
    simpa only [one_mul, mul_one] using h
  have hAbs := absorbProductEquiv_normBound eStable cZeroHeadTailEquiv
    hS1 (by norm_num) hStable equivNormBound_cZeroHeadTail
  have h := (hYX.trans hAbs hD0 (by positivity)).symm
  change EquivNormBound (cZeroDecompositionEquiv eX eXY eYX)
    (D * ((4 * D ^ 2) ^ 2 * 2)) at h
  convert h using 1; ring

end ThesisCommon
