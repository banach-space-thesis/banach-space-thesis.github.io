import ThesisCommon.Analysis.SchauderMatrix
import ThesisCommon.Analysis.SchauderOperators
import ThesisCommon.Analysis.SharpFactorization

/-! Reciprocal diagonal factorisation on a one-unconditional Schauder basis.
Symmetry is unnecessary once every diagonal entry is bounded away from zero.
-/
noncomputable section
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]
variable (b : NormalizedSchauderBasis 𝕜 X)

theorem diagonal_factors_of_half_le (hb : b.IsOneUnconditional)
    (D : X →L[𝕜] X) (d : ℕ → 𝕜)
    (hD : ∀ n, D (b.vector n) = d n • b.vector n)
    (hd : ∀ n, (1 / 2 : ℝ) ≤ ‖d n‖) : FactorsIdentityWith D X 2 := by
  have hinv (n : ℕ) : ‖(d n)⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hd n))]
    linarith [hd n]
  obtain ⟨R, hR, hRe⟩ := b.exists_diagonal hb (fun n => (d n)⁻¹) (by norm_num) hinv
  refine ⟨R, ContinuousLinearMap.id 𝕜 X, ?_, ?_⟩
  · apply b.operator_ext
    intro n
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      hD, map_smul, hRe, smul_smul]
    have hn : d n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hd n))
    rw [mul_inv_cancel₀ hn, one_smul]
  · have hi : ‖ContinuousLinearMap.id 𝕜 X‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa only [mul_one] using mul_le_mul hR hi (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)

/-- Construct the bounded diagonal model from actual entries. Geometric
off-diagonal bounds control the operator norm of the remainder. -/
theorem diagonal_model_of_large_entries (hb : b.IsOneUnconditional)
    (S : X →L[𝕜] X) {η : ℝ} (hη : 0 < η)
    (hd : ∀ n, (1 / 2 : ℝ) ≤ ‖b.coord n (S (b.vector n))‖)
    (he : ∀ i j, i ≠ j → ‖b.coord i (S (b.vector j))‖ ≤ η / (2 : ℝ) ^ (i + j + 2)) :
    ∃ D : X →L[𝕜] X, FactorsIdentityWith D X 2 ∧ ‖S - D‖ ≤ η := by
  let d : ℕ → 𝕜 := fun n => b.coord n (S (b.vector n))
  have hdnorm (n : ℕ) : ‖d n‖ ≤ ‖S‖ := by
    calc
      _ ≤ ‖S (b.vector n)‖ := b.coord_le_norm hb n _
      _ ≤ ‖S‖ * ‖b.vector n‖ := S.le_opNorm _
      _ = ‖S‖ := by rw [b.norm_vector, mul_one]
  obtain ⟨D, _, hD⟩ := b.exists_diagonal hb d (norm_nonneg S) hdnorm
  refine ⟨D, b.diagonal_factors_of_half_le hb D d hD hd, ?_⟩
  apply b.norm_le_of_geometric_entries hb _ hη.le
  intro i j
  simp only [ContinuousLinearMap.sub_apply, map_sub, hD, map_smul,
    b.biorthogonal, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, mul_one]
    change ‖d i - d i‖ ≤ _
    rw [sub_self, norm_zero]
    positivity
  · simp only [if_neg hij, mul_zero, sub_zero]
    exact he i j hij

end NormalizedSchauderBasis
end ThesisCommon
