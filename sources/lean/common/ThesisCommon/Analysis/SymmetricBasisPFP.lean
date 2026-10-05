import ThesisCommon.Analysis.SchauderOperators
import ThesisCommon.Analysis.SchauderSelection
import ThesisCommon.Analysis.SharpFactorization

/-! Theorem 3.3: symmetric normalized bases not equivalent to ℓ₁ have
2⁺-PFP. All subsequence maps and diagonal multipliers are constructed from
the basis. The proof uses two-sided gliding humps, the infinite diagonal
branch, reciprocal multiplication, and the sharp Neumann correction.
-/
noncomputable section
open Filter Topology
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]
variable (b : NormalizedSchauderBasis 𝕜 X)

/-- An actual bounded operator acting diagonally on the basis vectors. -/
def IsDiagonal (D : X →L[𝕜] X) : Prop :=
  ∃ d : ℕ → 𝕜, ∀ n, D (b.vector n) = d n • b.vector n

/-- Large diagonal entries on an infinite subsequence give factors of norm
product at most two, by reciprocal diagonal multiplication. -/
theorem diagonal_factors_of_subsequence (hb : b.HasSymmetricNorm)
    (D : X →L[𝕜] X) (d : ℕ → 𝕜)
    (hD : ∀ n, D (b.vector n) = d n • b.vector n)
    (f : ℕ ↪ ℕ) (hd : ∀ n, (1 / 2 : ℝ) ≤ ‖d (f n)‖) :
    FactorsIdentityWith D X 2 := by
  obtain ⟨A, B, hAB, hA, hB, hBe, hAc⟩ := b.exists_subsequence_compression hb f
  have hinv (n : ℕ) : ‖(d (f n))⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hd n))]
    linarith [hd n]
  obtain ⟨R, hR, hRe⟩ := b.exists_diagonal hb.1 (fun n => (d (f n))⁻¹)
    (by norm_num) hinv
  have hAe (n : ℕ) : A (b.vector (f n)) = b.vector n := by
    have hh := DFunLike.congr_fun hAB (b.vector n)
    simpa only [ContinuousLinearMap.comp_apply, hBe, ContinuousLinearMap.id_apply] using hh
  refine ⟨R.comp A, B, ?_, ?_⟩
  · apply b.operator_ext
    intro n
    simp only [ContinuousLinearMap.comp_apply, hBe, hD, map_smul, hAe, hRe,
      smul_smul, ContinuousLinearMap.id_apply]
    have hn : d (f n) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hd n))
    rw [mul_inv_cancel₀ hn, one_smul]
  · have hRA : ‖R.comp A‖ ≤ 2 := by
      calc
        _ ≤ ‖R‖ * ‖A‖ := R.opNorm_comp_le A
        _ ≤ 2 * 1 := mul_le_mul hR hA (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    simpa only [mul_one] using mul_le_mul hRA hB (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)

/-- The infinite diagonal dichotomy, with the exact constant two. -/
theorem diagonal_dichotomy (hb : b.HasSymmetricNorm)
    (D : X →L[𝕜] X) (hD : b.IsDiagonal D) :
    FactorsIdentityWith D X 2 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - D) X 2 := by
  classical
  obtain ⟨d, hD⟩ := hD
  let M : Set ℕ := {n | (1 / 2 : ℝ) ≤ ‖d n‖}
  by_cases hM : M.Infinite
  · let f : ℕ ↪ ℕ := (hM.natEmbedding M).trans (Function.Embedding.subtype M)
    exact Or.inl (b.diagonal_factors_of_subsequence hb D d hD f
      (fun n => (hM.natEmbedding M n).property))
  · have hc : Mᶜ.Infinite := (Set.not_infinite.mp hM).infinite_compl
    let f : ℕ ↪ ℕ := (hc.natEmbedding Mᶜ).trans (Function.Embedding.subtype Mᶜ)
    apply Or.inr
    refine b.diagonal_factors_of_subsequence hb _ (fun n => 1 - d n) ?_ f ?_
    · intro n
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hD,
        sub_smul, one_smul]
    · intro n
      have hn : ¬ (1 / 2 : ℝ) ≤ ‖d (f n)‖ := (hc.natEmbedding Mᶜ n).property
      have hh := norm_add_le (d (f n)) (1 - d (f n))
      rw [add_sub_cancel, norm_one] at hh
      linarith

/-- Every bounded operator on the given symmetric basis has arbitrarily
accurate diagonal compression, with genuine contractive left inverse maps. -/
theorem approximate_diagonal_compression (hb : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (T : X →L[𝕜] X) {η : ℝ} (hη : 0 < η) :
    ∃ A B D : X →L[𝕜] X,
      A.comp B = ContinuousLinearMap.id 𝕜 X ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      b.IsDiagonal D ∧ ‖(A.comp T).comp B - D‖ < η := by
  obtain ⟨f, hf, _, hsmall⟩ := b.small_off_diagonal_subsequence
    (b.weakly_null_of_not_equivalentEllOne hb hnot) T Set.infinite_univ
    (show 0 < η / 2 by positivity)
  let e : ℕ ↪ ℕ := ⟨f, hf.injective⟩
  obtain ⟨A, B, hAB, hA, hB, hBe, hAc⟩ := b.exists_subsequence_compression hb e
  let S : X →L[𝕜] X := (A.comp T).comp B
  let d : ℕ → 𝕜 := fun n => b.coord n (S (b.vector n))
  have hd (n : ℕ) : ‖d n‖ ≤ ‖S‖ := by
    calc
      _ ≤ ‖S (b.vector n)‖ := b.coord_le_norm hb.1 n _
      _ ≤ ‖S‖ * ‖b.vector n‖ := S.le_opNorm _
      _ = ‖S‖ := by rw [b.norm_vector, mul_one]
  obtain ⟨D, _, hDe⟩ := b.exists_diagonal hb.1 d (norm_nonneg S) hd
  refine ⟨A, B, D, hAB, hA, hB, ⟨d, hDe⟩, ?_⟩
  have hnorm : ‖S - D‖ ≤ η / 2 := by
    apply b.norm_le_of_geometric_entries hb.1 _ (by positivity)
    intro i j
    simp only [ContinuousLinearMap.sub_apply, map_sub, hDe, map_smul,
      b.biorthogonal, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, mul_one]
      change ‖d i - d i‖ ≤ _
      rw [sub_self, norm_zero]
      positivity
    · simp only [if_neg hij, mul_zero, sub_zero]
      change ‖b.coord i (A (T (B (b.vector j))))‖ ≤ _
      rw [hAc, hBe]
      exact (hsmall i j hij).le
  exact hnorm.trans_lt (by linarith)

/-- The full 2⁺-PFP theorem. All inputs to the sharp perturbation assembly
are proved above from the original symmetric-basis hypotheses. -/
theorem hasCPlusPFP_two (hb : b.HasSymmetricNorm) (hnot : ¬ b.EquivalentEllOne) :
    HasCPlusPFP 𝕜 X 2 := by
  apply hasCPlusPFP_of_approximate_compressions (by norm_num : (0 : ℝ) < 2)
    b.IsDiagonal (b.diagonal_dichotomy hb)
  intro T η hη
  exact b.approximate_diagonal_compression hb hnot T hη

end NormalizedSchauderBasis
end ThesisCommon
