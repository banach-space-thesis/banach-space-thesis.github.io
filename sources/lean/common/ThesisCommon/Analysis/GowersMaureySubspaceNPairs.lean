import ThesisCommon.Analysis.GowersMaureyNPairs

/-! N-pair identities for operators on an actual subspace, with no assumed
extension of the operator to the whole space. The scalar normalization
is performed inside the original domain. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def normalizedPairSum {N : ℕ} (u : Fin N → E) : E :=
  ((logarithmicWeight N / N : ℝ) : 𝕜) • ∑ i, u i

theorem completedPairing_normalizedPairSum (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) (a : Fin N → C00 𝕜) (u : Fin N → E)
    (T : E →L[𝕜] ShiftSpace D) :
    completedPairing D (averagedPairFunctional a) (T (normalizedPairSum (𝕜 := 𝕜) u)) =
      (N : 𝕜)⁻¹ * ∑ i, ∑ j, completedPairing D (a i) (T (u j)) := by
  have hf : logarithmicWeight N ≠ 0 :=
    (zero_lt_one.trans_le (one_le_logarithmicWeight hN)).ne'
  have hNc : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hfc : (logarithmicWeight N : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hf
  have hsm (r : ℝ) (x : C00 𝕜) : r • x = (r : 𝕜) • x := by
    ext i
    simp only [Finsupp.smul_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  rw [averagedPairFunctional, normalizedPairSum, hsm]
  simp only [map_smul, map_sum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    smul_eq_mul, RCLike.ofReal_inv, RCLike.ofReal_div, RCLike.ofReal_natCast]
  rw [← Finset.mul_sum, ← mul_assoc]
  congr 1
  · field_simp
  · exact Finset.sum_comm

theorem normalizedPairSum_subspace_value (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) {N : ℕ} (u : Fin N → Y) (x : Fin N → C00 𝕜)
    (hx : ∀ i, (u i : ShiftSpace D) = denseEmbedding D (x i)) :
    (normalizedPairSum (𝕜 := 𝕜) (E := Y) u : ShiftSpace D) =
      denseEmbedding D (normalizedPairVector x) := by
  have hsm (r : ℝ) (x : C00 𝕜) : r • x = (r : 𝕜) • x := by
    ext i
    simp only [Finsupp.smul_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  change Y.subtypeL (normalizedPairSum (𝕜 := 𝕜) u) = _
  simp only [normalizedPairSum, normalizedPairVector, hsm, map_smul, map_sum,
    Submodule.subtypeL_apply, hx]

theorem normalizedPairSum_subspace_norm (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) {N : ℕ} (u : Fin N → Y) (x : Fin N → C00 𝕜)
    (hx : ∀ i, (u i : ShiftSpace D) = denseEmbedding D (x i)) :
    ‖normalizedPairSum (𝕜 := 𝕜) u‖ = implicitNorm D (normalizedPairVector x) := by
  change ‖(normalizedPairSum (𝕜 := 𝕜) (E := Y) u : ShiftSpace D)‖ = _
  rw [normalizedPairSum_subspace_value D Y u x hx, denseEmbedding_norm]
  rfl

theorem normalizedPairSum_offDiagonal_error (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) (a : Fin N → C00 𝕜) (u : Fin N → E)
    (T : E →L[𝕜] ShiftSpace D) :
    ‖completedPairing D (averagedPairFunctional a) (T (normalizedPairSum (𝕜 := 𝕜) u)) -
        (N : 𝕜)⁻¹ * ∑ i, completedPairing D (a i) (T (u i))‖ ≤
      (N : ℝ)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖completedPairing D (a i) (T (u j))‖ := by
  classical
  let b (i j : Fin N) := completedPairing D (a i) (T (u j))
  rw [completedPairing_normalizedPairSum D hN]
  change ‖(N : 𝕜)⁻¹ * ∑ i, ∑ j, b i j - (N : 𝕜)⁻¹ * ∑ i, b i i‖ ≤ _
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have he (i : Fin N) : (∑ j, b i j) - b i i = ∑ j ∈ Finset.univ.erase i, b i j := by
    have h := Finset.sum_erase_add Finset.univ (fun j => b i j) (Finset.mem_univ i)
    exact sub_eq_iff_eq_add.mpr h.symm
  simp_rw [he]
  rw [norm_mul, norm_inv, RCLike.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))

end ThesisCommon.GowersMaurey
