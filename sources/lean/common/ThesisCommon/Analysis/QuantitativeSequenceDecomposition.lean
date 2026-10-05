import ThesisCommon.Analysis.BoundedEquivalenceCalculus
import ThesisCommon.Analysis.PelczynskiDecomposition

/-! A deliberately generous bound for the existing concrete sequence
decomposition maps. These constants support uniform primariness transfer;
they are separate from the sharper printed Appendix A constants. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y A B V W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

theorem absorbProductEquiv_normBound (e : X ≃L[𝕜] X × (V × W)) (h : V ≃L[𝕜] A × V)
    {C D : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D)
    (he : EquivNormBound e C) (hh : EquivNormBound h D) :
    EquivNormBound (absorbProductEquiv e h) (C ^ 2 * D) := by
  have hC0 := zero_le_one.trans hC
  have hD0 := zero_le_one.trans hD
  have h₁ := he.prodCongr (equivNormBound_refl (𝕜 := 𝕜) (X := A) |>.mono hC) hC0
  have h₂ := equivNormBound_assoc (𝕜 := 𝕜) (X := X) (Y := V × W) (Z := A)
  have h₃ := hh.symm.prodCongr (equivNormBound_refl (𝕜 := 𝕜) (X := W) |>.mono hD) hD0
  have h₄ := (equivNormBound_assoc (𝕜 := 𝕜) (X := A) (Y := V) (Z := W)).symm.trans
    h₃ zero_le_one hD0
  have h₅ := (equivNormBound_comm (𝕜 := 𝕜) (X := V × W) (Y := A)).trans
    h₄ zero_le_one (by simpa only [one_mul] using hD0)
  have h₅' : EquivNormBound
      ((ContinuousLinearEquiv.prodComm 𝕜 (V × W) A).trans
        ((ContinuousLinearEquiv.prodAssoc 𝕜 A V W).symm.trans
          (h.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 W)))) D := by
    simpa only [one_mul] using h₅
  have h₆ := (equivNormBound_refl (𝕜 := 𝕜) (X := X) |>.mono hD).prodCongr h₅' hD0
  have h₇ := h₆.trans he.symm hD0 hC0
  have h₈ := h₂.trans h₇ zero_le_one (mul_nonneg hD0 hC0)
  have h₉ := h₁.trans h₈ hC0 (by simpa only [one_mul] using mul_nonneg hD0 hC0)
  change EquivNormBound (absorbProductEquiv e h) (C * (1 * (D * C))) at h₉
  convert h₉ using 1; ring

/-- With an isometric countable self-similarity and two decompositions
bounded in both directions by D, the actual lp decomposition map has
both norms at most 32 D^5. This works also at p=∞ and for zero spaces. -/
theorem lpDecompositionEquiv_normBound (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (eX : X ≃L[𝕜] lp (fun _ : ℕ => X) p)
    (eXY : X ≃L[𝕜] Y × B) (eYX : Y ≃L[𝕜] X × A)
    {D : ℝ} (hD : 1 ≤ D) (hX : EquivNormBound eX 1)
    (hXY : EquivNormBound eXY D) (hYX : EquivNormBound eYX D) :
    EquivNormBound (lpDecompositionEquiv p eX eXY eYX) (32 * D ^ 5) := by
  have hD0 := zero_le_one.trans hD
  have hD2 : 1 ≤ D * D := by nlinarith
  let e := eXY.trans (eYX.prodCongr (ContinuousLinearEquiv.refl 𝕜 B))
  have he : EquivNormBound e (D * D) :=
    hXY.trans (hYX.prodCongr (equivNormBound_refl |>.mono hD) hD0) hD0 hD0
  let eSum := (lpMapEquiv (ι := ℕ) p e).trans
    ((lpProdEquiv p).trans
      (((lpProdEquiv p).prodCongr
        (ContinuousLinearEquiv.refl 𝕜 (lp (fun _ : ℕ => B) p))).trans
          (ContinuousLinearEquiv.prodAssoc 𝕜 _ _ _)))
  have h₂ := (equivNormBound_lpProd (𝕜 := 𝕜) (X := X) (Y := A) p).prodCongr
    (equivNormBound_refl (𝕜 := 𝕜) (X := lp (fun _ : ℕ => B) p) |>.mono (by norm_num))
    (by norm_num : (0 : ℝ) ≤ 2)
  have h₃ := h₂.trans (equivNormBound_assoc (𝕜 := 𝕜)) (by norm_num) zero_le_one
  have h₄ := (equivNormBound_lpProd (𝕜 := 𝕜) (X := X × A) (Y := B) p).trans
    h₃ (by norm_num) (by norm_num)
  have hSum : EquivNormBound eSum (4 * D ^ 2) := by
    have h := (he.lpMap (mul_nonneg hD0 hD0) p).trans h₄
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
  have hAbs := absorbProductEquiv_normBound eStable (lpHeadTailEquiv p)
    hS1 (by norm_num) hStable (equivNormBound_lpHeadTail p)
  have h := (hYX.trans hAbs hD0 (by positivity)).symm
  change EquivNormBound (lpDecompositionEquiv p eX eXY eYX)
    (D * ((4 * D ^ 2) ^ 2 * 2)) at h
  convert h using 1; ring

end ThesisCommon
