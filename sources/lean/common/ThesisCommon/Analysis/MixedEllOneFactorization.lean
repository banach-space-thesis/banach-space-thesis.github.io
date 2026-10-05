import ThesisCommon.Analysis.MixedEllOneSelection
import ThesisCommon.Analysis.SchauderSumDiagonal

/-! Arbitrarily accurate diagonal compression and 2-plus-PFP for X(ell_1).
The asymmetric entry budget is summed in the target inner coordinate before
the checked block estimate is applied. Canonical product retractions and the
diagonal dichotomy supply every input to the sharp Neumann correction.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem norm_le_of_ellOne_geometric_entries
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ r s i j, ‖ellOneEntry T r s i j‖ ≤ ε / (2 : ℝ) ^ (r + i + s + 3)) :
    ‖T‖ ≤ ε := by
  apply norm_le_of_geometric_blocks T hε
  intro r i
  have hg : HasSum (fun s : ℕ => ε / (2 : ℝ) ^ (r + i + s + 3))
      (ε / (2 : ℝ) ^ (r + i + 2)) := by
    convert NormalizedSchauderBasis.hasSum_half_geometric.mul_left
      (ε / (2 : ℝ) ^ (r + i + 2)) using 1
    · funext s
      simp only [div_eq_mul_inv, pow_add, inv_pow, one_mul]
      ring
    · simp only [mul_one]
  apply ellOne_norm_le_of_columns (block T r i) (by positivity)
  intro j
  calc
    _ = ∑' s, ‖ellOneEntry T r s i j‖ := ellOne_norm_eq_tsum _
    _ ≤ ∑' s, ε / (2 : ℝ) ^ (r + i + s + 3) :=
      Summable.tsum_le_tsum (fun s => hT r s i j)
        (ellOne_hasSum_norm ((block T r i) (lp.single 1 j (1 : 𝕜)))).summable hg.summable
    _ = _ := hg.tsum_eq

theorem ellOne_approximate_diagonal_compression (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) {η : ℝ} (hη : 0 < η) :
    ∃ A B D : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
        SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1),
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      IsProductDiagonal (scalarLpSchauderBasis 1 (by simp)) D ∧
      ‖(A.comp T).comp B - D‖ < η := by
  let c := scalarLpSchauderBasis (𝕜 := 𝕜) 1 (by simp)
  have hc : c.HasSymmetricNorm := scalarLpSchauderBasis_symmetric 1 (by simp)
  obtain ⟨n, m, hn, hm, hsmall⟩ := ellOne_asymmetric_selection hs hnot T
    (show 0 < η / 2 by positivity)
  obtain ⟨A, B, hAB, hA, hB, hBv, hAc⟩ := exists_product_compression hs c hc
    ⟨n, hn.injective⟩ (fun i => ⟨m i, (hm i).injective⟩)
  let S := (A.comp T).comp B
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let β := productBasis (b := b) (hb := hb) c hc.1 e
  have hβ : β.IsOneUnconditional := productBasis_oneUnconditional c hc.1 e
  let d := fun k => β.coord k (S (β.vector k))
  have hd (k : ℕ) : ‖d k‖ ≤ ‖S‖ := by
    calc
      _ ≤ ‖S (β.vector k)‖ := β.coord_le_norm hβ k _
      _ ≤ ‖S‖ * ‖β.vector k‖ := S.le_opNorm _
      _ = ‖S‖ := by rw [β.norm_vector, mul_one]
  obtain ⟨D, _, hDe⟩ := β.exists_diagonal hβ d (norm_nonneg S) hd
  have hD (p : ℕ × ℕ) : D (productVector c p) =
      productCoordinate c p (S (productVector c p)) • productVector c p := by
    have hh := hDe (e.symm p)
    change D (productVector c (e (e.symm p))) =
      productCoordinate c (e (e.symm p)) (S (productVector c (e (e.symm p)))) •
        productVector c (e (e.symm p)) at hh
    simpa only [e.apply_symm_apply] using hh
  refine ⟨A, B, D, hAB, hA, hB, ⟨_, hD⟩, ?_⟩
  have hnorm : ‖S - D‖ ≤ η / 2 := by
    apply norm_le_of_ellOne_geometric_entries _ (by positivity)
    intro r s i j
    rw [ellOneEntry_eq_productCoordinate]
    change ‖productCoordinate c (r, s) ((S - D) (productVector c (i, j)))‖ ≤ _
    simp only [ContinuousLinearMap.sub_apply, map_sub, hD, map_smul,
      product_biorthogonal, smul_eq_mul]
    by_cases hp : (r, s) = (i, j)
    · rw [if_pos hp, mul_one, hp, sub_self, norm_zero]
      positivity
    · rw [if_neg hp, mul_zero, sub_zero]
      change ‖productCoordinate c (r, s) (A (T (B (productVector c (i, j)))))‖ ≤ _
      rw [hAc, hBv]
      exact hsmall r s i j hp
  exact hnorm.trans_lt (by linarith)

/-- Full mixed-sum theorem, over real or complex scalars. Only the outer
basis is required to be non-ell_1. Every selection and model input is proved. -/
theorem ellOne_hasCPlusPFP_two (hs : b.HasSymmetricNorm) (hnot : ¬ b.EquivalentEllOne) :
    HasCPlusPFP 𝕜 (SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) 2 := by
  let c := scalarLpSchauderBasis (𝕜 := 𝕜) 1 (by simp)
  apply hasCPlusPFP_of_approximate_compressions (by norm_num : (0 : ℝ) < 2)
    (IsProductDiagonal c)
    (fun D hD => product_diagonal_dichotomy hs c (scalarLpSchauderBasis_symmetric 1 (by simp)) D hD)
  intro T η hη
  exact ellOne_approximate_diagonal_compression hs hnot T hη

end SchauderSum
end ThesisCommon
