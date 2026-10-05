import ThesisCommon.Analysis.GowersMaureyCompletedPairing
import ThesisCommon.Analysis.GowersMaureyRISLemmaSeven
import ThesisCommon.Analysis.GowersMaureyNormingForms

/-! Actual normalized vector--functional pairs from the proof of Lemma 8.
The pairing identity is on the completed space and applies to every
bounded operator. The off-diagonal error is kept explicitly. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def normalizedPairVector {N : ℕ} (u : Fin N → C00 𝕜) : C00 𝕜 :=
  (logarithmicWeight N / N) • ∑ i, u i

def averagedPairFunctional {N : ℕ} (a : Fin N → C00 𝕜) : C00 𝕜 :=
  (logarithmicWeight N)⁻¹ • ∑ i, a i

theorem averagedPairFunctional_mem {D : ConstructionData 𝕜} {N : ℕ}
    (hN : 0 < N) {a : Fin N → C00 𝕜} (ha : Successive a)
    (hu : ∀ i, DualUnit (implicitNorm D) (a i)) :
    AveragedFunctional (implicitNorm D) N (averagedPairFunctional a) :=
  ⟨hN,a,ha,hu,rfl⟩

theorem normalizedPairVector_norm_le_four {D : ConstructionData 𝕜} {N : ℕ}
    {u : Fin N → C00 𝕜} (h : IsRIS D 1 u) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ))) :
    implicitNorm D (normalizedPairVector u) ≤ 4 := by
  obtain ⟨h⟩ := h
  have hb := h.normalized_norm_le_lemma7 m hN
  norm_num at hb
  exact hb

theorem completedPairing_normalizedPairVector (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) (a u : Fin N → C00 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    completedPairing D (averagedPairFunctional a)
        (T (denseEmbedding D (normalizedPairVector u))) =
      (N : 𝕜)⁻¹ * ∑ i, ∑ j, completedPairing D (a i) (T (denseEmbedding D (u j))) := by
  have hf : logarithmicWeight N ≠ 0 :=
    (zero_lt_one.trans_le (one_le_logarithmicWeight hN)).ne'
  have hNc : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hfc : (logarithmicWeight N : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hf
  have hsm (r : ℝ) (x : C00 𝕜) : r • x = (r : 𝕜) • x := by
    ext i
    simp only [Finsupp.smul_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  rw [averagedPairFunctional, normalizedPairVector, hsm, hsm]
  simp only [map_smul,
    map_sum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    smul_eq_mul, RCLike.ofReal_inv, RCLike.ofReal_div, RCLike.ofReal_natCast]
  rw [← Finset.mul_sum, ← mul_assoc]
  congr 1
  · field_simp
  · exact Finset.sum_comm

theorem normalizedPair_offDiagonal_error (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) (a u : Fin N → C00 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    ‖completedPairing D (averagedPairFunctional a)
        (T (denseEmbedding D (normalizedPairVector u))) -
        (N : 𝕜)⁻¹ * ∑ i, completedPairing D (a i) (T (denseEmbedding D (u i)))‖ ≤
      (N : ℝ)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ‖completedPairing D (a i) (T (denseEmbedding D (u j)))‖ := by
  classical
  let b (i j : Fin N) := completedPairing D (a i) (T (denseEmbedding D (u j)))
  rw [completedPairing_normalizedPairVector D hN]
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
