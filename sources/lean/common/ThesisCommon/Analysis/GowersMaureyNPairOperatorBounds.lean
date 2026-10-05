import ThesisCommon.Analysis.GowersMaureySubspaceNPairs

/-! Quantitative N-pair operator evaluations with the genuine sum of
off-diagonal errors. Both the detecting operator and the finite orbit
operators may have the original subspace as their domain. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem normalizedPairSum_error_le_of_row_bounds (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) (a : Fin N → C00 𝕜) (u : Fin N → E)
    (T : E →L[𝕜] ShiftSpace D) {η : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖completedPairing D (a i) (T (u j))‖ ≤ η) :
    ‖completedPairing D (averagedPairFunctional a) (T (normalizedPairSum (𝕜 := 𝕜) u)) -
        (N : 𝕜)⁻¹ * ∑ i, completedPairing D (a i) (T (u i))‖ ≤ η := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  apply (normalizedPairSum_offDiagonal_error D hN a u T).trans
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, η :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hrow i))
        (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = η := by simp [hNr]

theorem normalizedPairSum_re_lower_bound (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) (a : Fin N → C00 𝕜) (u : Fin N → E)
    (T : E →L[𝕜] ShiftSpace D) {ε η : ℝ}
    (hdiag : ∀ i, ε ≤ RCLike.re (completedPairing D (a i) (T (u i))))
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖completedPairing D (a i) (T (u j))‖ ≤ η) :
    ε-η ≤ RCLike.re (completedPairing D (averagedPairFunctional a)
      (T (normalizedPairSum (𝕜 := 𝕜) u))) := by
  let z := completedPairing D (averagedPairFunctional a) (T (normalizedPairSum (𝕜 := 𝕜) u))
  let d := (N : 𝕜)⁻¹ * ∑ i, completedPairing D (a i) (T (u i))
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlow : ε ≤ RCLike.re d := by
    have heN : (N : 𝕜)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : 𝕜) := by simp
    dsimp only [d]
    rw [heN, RCLike.re_ofReal_mul, map_sum]
    calc
      ε = (N : ℝ)⁻¹ * ∑ _i : Fin N, ε := by simp [hNr]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hdiag i))
        (inv_nonneg.mpr (Nat.cast_nonneg N))
  have herr : ‖z-d‖ ≤ η := normalizedPairSum_error_le_of_row_bounds D hN a u T hrow
  have hr := RCLike.re_le_norm (d-z)
  rw [map_sub, norm_sub_rev] at hr
  change ε-η ≤ RCLike.re z
  linarith

theorem normalizedPairSum_norm_le_of_row_bounds (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) (a : Fin N → C00 𝕜) (u : Fin N → E)
    (T : E →L[𝕜] ShiftSpace D) {δ η : ℝ}
    (hdiag : ∀ i, ‖completedPairing D (a i) (T (u i))‖ ≤ δ)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖completedPairing D (a i) (T (u j))‖ ≤ η) :
    ‖completedPairing D (averagedPairFunctional a) (T (normalizedPairSum (𝕜 := 𝕜) u))‖ ≤ δ+η := by
  let z := completedPairing D (averagedPairFunctional a) (T (normalizedPairSum (𝕜 := 𝕜) u))
  let d := (N : 𝕜)⁻¹ * ∑ i, completedPairing D (a i) (T (u i))
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd : ‖d‖ ≤ δ := by
    dsimp only [d]
    rw [norm_mul, norm_inv, RCLike.norm_natCast]
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, δ := mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hdiag i)))
        (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ = δ := by simp [hNr]
  have herr : ‖z-d‖ ≤ η := normalizedPairSum_error_le_of_row_bounds D hN a u T hrow
  change ‖z‖ ≤ δ+η
  calc
    ‖z‖ = ‖(z-d)+d‖ := by rw [sub_add_cancel]
    _ ≤ ‖z-d‖+‖d‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end ThesisCommon.GowersMaurey
