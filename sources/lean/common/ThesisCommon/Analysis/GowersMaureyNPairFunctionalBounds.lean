import ThesisCommon.Analysis.GowersMaureySubspaceNPairs

/-! Functional bounds on genuine normalized finite sums. This retains
arbitrary normed domains, so a later recursive selection can control every
previous functional composed with the original subspace operator. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem normalizedPairSum_functional_bound {N : ℕ} (hN : 0 < N)
    (u : Fin N → E) (φ : E →L[𝕜] 𝕜) {δ : ℝ}
    (hbound : ∀ i, ‖φ (u i)‖ ≤ δ) :
    ‖φ (normalizedPairSum (𝕜 := 𝕜) u)‖ ≤ logarithmicWeight N * δ := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hf : 0 ≤ logarithmicWeight N / N :=
    div_nonneg (logarithmicWeight_nonneg N) (Nat.cast_nonneg N)
  rw [normalizedPairSum, map_smul, map_sum, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg hf]
  calc
    _ ≤ (logarithmicWeight N / N) * ∑ _i : Fin N, δ :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun i _ => hbound i))) hf
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; field_simp

end ThesisCommon.GowersMaurey
