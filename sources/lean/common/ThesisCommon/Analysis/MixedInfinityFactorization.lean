import ThesisCommon.Analysis.MixedInfinityRepresentation
import ThesisCommon.Analysis.MixedInfinitySelection
import ThesisCommon.Analysis.MixedInfinityDiagonal

/-! Full 2-plus-PFP for the genuine X(ell_infinity). Restricted matrix
representation is established before estimating any infinite-coordinate
remainder. The outer geometric budget is then summed in the actual norm. -/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem infinity_remainder_hasSum
    {T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)} (hT : HasInfinityMatrix T)
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j : ℕ) :
    HasSum (fun p : ℕ × ℕ => if p = (i, j) then 0 else
      x p.1 p.2 * infinityEntry T i j p.1 p.2) ((T - infinityDiagonalPart T) x i j) := by
  classical
  have hh := (hT x i j).sub
    (hasSum_ite_eq (i, j) (x i j * infinityEntry T i j i j))
  convert hh using 1
  · funext p
    by_cases hp : p = (i, j) <;> simp [hp]
  · change T x i j - infinityDiagonalPart T x i j = _
    rw [infinityDiagonalPart_apply]

theorem infinity_remainder_norm_le
    {T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)} (hT : HasInfinityMatrix T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ i j, Summable (fun p : ℕ × ℕ => if p = (i, j) then 0 else
        ‖infinityEntry T i j p.1 p.2‖) ∧
      (∑' p : ℕ × ℕ, if p = (i, j) then 0 else ‖infinityEntry T i j p.1 p.2‖) ≤
        ε / (2 : ℝ) ^ (i + 1)) : ‖T - infinityDiagonalPart T‖ ≤ ε := by
  classical
  let R := T - infinityDiagonalPart T
  apply R.opNorm_le_bound hε
  intro x
  have hrow (i : ℕ) : ‖R x i‖ ≤ ε / (2 : ℝ) ^ (i + 1) * ‖x‖ := by
    apply lp.norm_le_of_forall_le (by positivity)
    intro j
    have hcoord : ‖R x i j‖ ≤ ‖x‖ *
        ∑' p : ℕ × ℕ, if p = (i, j) then 0 else ‖infinityEntry T i j p.1 p.2‖ := by
      apply (infinity_remainder_hasSum hT x i j).norm_le_of_bounded
        ((hsmall i j).1.hasSum.mul_left ‖x‖)
      intro p
      by_cases hp : p = (i, j)
      · simp only [if_pos hp, norm_zero, mul_zero, le_refl]
      · simp only [if_neg hp, norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((lp.norm_apply_le_norm ENNReal.top_ne_zero (x p.1) p.2).trans (norm_apply_le x p.1))
          (norm_nonneg _)
    exact hcoord.trans ((mul_le_mul_of_nonneg_left (hsmall i j).2 (norm_nonneg x)).trans_eq
      (mul_comm _ _))
  rw [norm_def]
  have hmajor := b.norm_le_of_coordinate_majorant (normVector (R x))
    (NormalizedSchauderBasis.hasSum_half_geometric.mul_left (ε * ‖x‖))
  rw [mul_one] at hmajor
  apply hmajor
  intro i
  rw [coord_normVector, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  convert hrow i using 1
  simp only [div_eq_mul_inv, pow_add, inv_pow, pow_one, one_mul]
  ring

theorem infinity_approximate_diagonal_compression (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) {η : ℝ} (hη : 0 < η) :
    ∃ A B D : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
        SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞),
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      IsInfinityDiagonal D ∧ ‖(A.comp T).comp B - D‖ < η := by
  obtain ⟨A₁, B₁, hAB₁, hA₁, hB₁, hrep⟩ := exists_infinity_matrix_compression hs T
  let S := (A₁.comp T).comp B₁
  obtain ⟨n, m, hn, hm, hsmall⟩ := infinity_small_cross_interaction hs hnot S
    (show 0 < η / 2 by positivity)
  let n' : ℕ ↪ ℕ := ⟨n, hn.injective⟩
  let m' : ℕ → ℕ ↪ ℕ := fun i => ⟨m i, (hm i).injective⟩
  let A₂ := infinityRestrict (hb := hb) hs n' m'
  let B₂ := infinityExtend (hb := hb) hs n' m'
  let U := (A₂.comp S).comp B₂
  have hAB₂ : A₂.comp B₂ = ContinuousLinearMap.id 𝕜 _ := infinityRestrict_comp_extend hs n' m'
  have hA₂ : ‖A₂‖ ≤ 1 := norm_infinityRestrict_le hs n' m'
  have hB₂ : ‖B₂‖ ≤ 1 := norm_infinityExtend_le hs n' m'
  have hU : HasInfinityMatrix U := hrep.compression hs n' m'
  have hbound : ‖U - infinityDiagonalPart U‖ ≤ η / 2 := by
    apply infinity_remainder_norm_le hU (by positivity)
    intro i j
    have hh := hsmall i j
    change _ ∧ _ ≤ _
    simp only [U, A₂, B₂, infinityEntry_compression]
    exact ⟨hh.1, hh.2.le⟩
  have hcomp : ((A₂.comp A₁).comp T).comp (B₁.comp B₂) = U := by
    simp only [U, S, ContinuousLinearMap.comp_assoc]
  refine ⟨A₂.comp A₁, B₁.comp B₂, infinityDiagonalPart U, ?_, ?_, ?_,
    isInfinityDiagonal_infinityDiagonalPart U, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change A₂ (A₁ (B₁ (B₂ x))) = x
    have h₁ := DFunLike.congr_fun hAB₁ (B₂ x)
    have h₂ := DFunLike.congr_fun hAB₂ x
    change A₁ (B₁ (B₂ x)) = B₂ x at h₁
    change A₂ (B₂ x) = x at h₂
    rw [h₁, h₂]
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hA₂ hA₁ (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hB₁ hB₂ (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  · rw [hcomp]
    exact hbound.trans_lt (by linarith)

theorem infinity_hasCPlusPFP_two (hs : b.HasSymmetricNorm) (hnot : ¬ b.EquivalentEllOne) :
    HasCPlusPFP 𝕜 (SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) 2 := by
  apply hasCPlusPFP_of_approximate_compressions (by norm_num : (0 : ℝ) < 2) IsInfinityDiagonal
  · exact fun D hD => infinity_diagonal_dichotomy hs D hD
  · intro T η hη
    exact infinity_approximate_diagonal_compression hs hnot T hη

end SchauderSum
end ThesisCommon
