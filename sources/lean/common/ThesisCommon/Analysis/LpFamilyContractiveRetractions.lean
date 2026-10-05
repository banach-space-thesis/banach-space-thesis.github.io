import ThesisCommon.Analysis.LpFamilyDiagonal

/-! Contractive coordinate retractions assemble into an actual retraction
of a dependent lp family, and survive an injective enlargement of its index. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 ι κ : Type*} [RCLike 𝕜]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lpFamily_exists_contractive_retraction (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ι ↪ κ) (J : ∀ i, E i →ₗᵢ[𝕜] X) (R : ∀ i, X →L[𝕜] E i)
    (hR : ∀ i, ‖R i‖ ≤ 1)
    (hRJ : ∀ i, (R i).comp (J i).toContinuousLinearMap = ContinuousLinearMap.id 𝕜 (E i)) :
    ∃ (A : lp E p →ₗᵢ[𝕜] lp (fun _ : κ => X) p)
      (B : lp (fun _ : κ => X) p →L[𝕜] lp E p),
      ‖B‖ ≤ 1 ∧ B.comp A.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 (lp E p) := by
  have hJ (i : ι) : ‖(J i).toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using (J i).norm_map x |>.le
  let A₀ : lp E p →L[𝕜] lp (fun _ : ι => X) p :=
    lpFamilyDiagonal (fun i => (J i).toContinuousLinearMap) 1 zero_le_one hJ
  let B₀ : lp (fun _ : ι => X) p →L[𝕜] lp E p :=
    lpFamilyDiagonal R 1 zero_le_one hR
  have hA₀ : ‖A₀‖ ≤ 1 := lpFamilyDiagonal_norm_le _ _ _ _
  have hB₀ : ‖B₀‖ ≤ 1 := lpFamilyDiagonal_norm_le _ _ _ _
  let A : lp E p →L[𝕜] lp (fun _ : κ => X) p := (lpExtend p e).comp A₀
  let B : lp (fun _ : κ => X) p →L[𝕜] lp E p := B₀.comp (lpRestrict p e)
  have hA : ‖A‖ ≤ 1 := by
    calc
      _ ≤ ‖lpExtend (𝕜 := 𝕜) (X := X) p e‖ * ‖A₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_lpExtend_le e) hA₀ (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hB : ‖B‖ ≤ 1 := by
    calc
      _ ≤ ‖B₀‖ * ‖lpRestrict (𝕜 := 𝕜) (X := X) p e‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hB₀ (norm_lpRestrict_le e) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hBA : B.comp A = ContinuousLinearMap.id 𝕜 (lp E p) := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change R i (lpExtend (𝕜 := 𝕜) p e (A₀ x) (e i)) = x i
    rw [lpExtend_apply_image]
    exact DFunLike.congr_fun (hRJ i) (x i)
  have hnorm (x : lp E p) : ‖A x‖ = ‖x‖ := by
    apply le_antisymm
    · exact (A.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right hA (norm_nonneg x))
    · have hx := DFunLike.congr_fun hBA x
      change B (A x) = x at hx
      calc
        ‖x‖ = ‖B (A x)‖ := congrArg norm hx.symm
        _ ≤ ‖B‖ * ‖A x‖ := B.le_opNorm _
        _ ≤ ‖A x‖ := by simpa using mul_le_mul_of_nonneg_right hB (norm_nonneg (A x))
  exact ⟨{ A.toLinearMap with norm_map' := hnorm }, B, hB, hBA⟩

end ThesisCommon
