import ThesisCommon.Analysis.IteratedTreeSelection
import ThesisCommon.Analysis.SchauderLargeDiagonal

/-! The analytic conclusion of CKL selection. Contractive subtree
compression has a uniformly invertible diagonal and arbitrarily small
remainder. The sharp Neumann correction gives every constant 2+epsilon.
-/
noncomputable section
universe u v
namespace ThesisCommon
variable {𝕜 : Type u} [RCLike 𝕜]

theorem iterated_supported_diagonal_compression (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (h : ∀ F ∈ first :: tail, F.basis.HasSymmetricNorm ∧ ¬ F.basis.EquivalentEllOne)
    (T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier)
    (hs : InfinitelySupported (tail.length + 1) (fun t => (1 / 2 : ℝ) ≤
      ‖iteratedBasisCoordinate first tail t (T (iteratedBasisVector first tail t))‖))
    {η : ℝ} (hη : 0 < η) :
    ∃ A B D : (iteratedSchauderSum first tail).Carrier →L[𝕜]
        (iteratedSchauderSum first tail).Carrier,
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      FactorsIdentityWith D (iteratedSchauderSum first tail).Carrier 2 ∧
      ‖(A.comp T).comp B - D‖ < η := by
  obtain ⟨f, hd, he⟩ := iterated_tree_selection first tail h T
    (show 0 < η / 2 by positivity) hs
  obtain ⟨A, B, hAB, hA, hB, hBe, hAc⟩ :=
    exists_iterated_tree_compression first tail (fun F hF => (h F hF).1) f
  let b := (iteratedUnconditionalBasis first tail).val
  let S := (A.comp T).comp B
  have hm (i j : ℕ) : b.coord i (S (b.vector j)) =
      iteratedBasisCoordinate first tail (f.map (natTupleEnumeration tail.length i))
        (T (iteratedBasisVector first tail (f.map (natTupleEnumeration tail.length j)))) := by
    dsimp only [b, S]
    rw [iteratedUnconditionalBasis_coord, iteratedUnconditionalBasis_vector]
    simp only [ContinuousLinearMap.comp_apply, hBe, hAc]
  have hdiag (i : ℕ) : (1 / 2 : ℝ) ≤ ‖b.coord i (S (b.vector i))‖ := by
    rw [hm]
    exact hd _
  have hoff (i j : ℕ) (hij : i ≠ j) :
      ‖b.coord i (S (b.vector j))‖ ≤ (η / 2) / (2 : ℝ) ^ (i + j + 2) := by
    rw [hm]
    apply (he i j hij).le.trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨D, hD, hnorm⟩ := b.diagonal_model_of_large_entries
    (iteratedUnconditionalBasis first tail).property S (by positivity : 0 < η / 2) hdiag hoff
  exact ⟨A, B, D, hAB, hA, hB, hD, hnorm.trans_lt (by linarith)⟩

theorem iterated_supported_factorization (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (h : ∀ F ∈ first :: tail, F.basis.HasSymmetricNorm ∧ ¬ F.basis.EquivalentEllOne)
    (T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier)
    (hs : InfinitelySupported (tail.length + 1) (fun t => (1 / 2 : ℝ) ≤
      ‖iteratedBasisCoordinate first tail t (T (iteratedBasisVector first tail t))‖))
    {ε : ℝ} (hε : 0 < ε) :
    FactorsIdentityWith T (iteratedSchauderSum first tail).Carrier (2 + ε) := by
  let r := ε / (2 + ε)
  have hden : 0 < 2 + ε := by linarith
  have hrpos : 0 < r := div_pos hε hden
  have hr : r < 1 := (div_lt_one hden).mpr (by linarith)
  have hconst : 2 / (1 - r) = 2 + ε := by
    apply (div_eq_iff (sub_pos.mpr hr).ne').mpr
    dsimp [r]
    field_simp [hden.ne']
    ring
  obtain ⟨A, B, D, _, hA, hB, hD, he⟩ :=
    iterated_supported_diagonal_compression first tail h T hs
      (show 0 < r / 2 by positivity)
  have hsmall : 2 * ‖(A.comp T).comp B - D‖ ≤ r := by linarith
  have hp : FactorsIdentityWith ((A.comp T).comp B)
      (iteratedSchauderSum first tail).Carrier (2 + ε) := by
    simpa only [hconst] using hD.perturb_fraction hr hsmall
  apply (hp.of_compression A B).mono
  have hn : ‖A‖ * ‖B‖ ≤ 1 := by
    simpa using mul_le_mul hA hB (norm_nonneg _) zero_le_one
  simpa using mul_le_mul_of_nonneg_left hn hden.le

end ThesisCommon
