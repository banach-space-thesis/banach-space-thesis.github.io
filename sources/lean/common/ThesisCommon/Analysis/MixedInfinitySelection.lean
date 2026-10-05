import ThesisCommon.Analysis.MixedInfinityEstimates
import ThesisCommon.Analysis.AsymmetricMatrixFusion

/-! The mixed ell_infinity recursion is the transposed scalar-array version
of the checked asymmetric selection. This constructs no transpose operator.
The source budget uses positive indices, translated here by adding five. -/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem infinity_asymmetric_selection (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ → ℕ) (m : ℕ → ℕ → ℕ), StrictMono n ∧ (∀ i, StrictMono (m i)) ∧
      ∀ i j r s, (i, j) ≠ (r, s) →
        ‖infinityEntry T (n i) (m i j) (n r) (m r s)‖ ≤
          ε / (2 : ℝ) ^ (i + r + s + 5) := by
  obtain ⟨n, m, hn, hm, hsmall⟩ := asymmetric_matrix_selection
    (fun p q => ‖infinityEntry T q.1 q.2 p.1 p.2‖)
    (fun p i => ε / (2 : ℝ) ^ (i + p.1 + p.2 + 5)) (by intros; positivity)
    (fun p η hη => infinity_finite_interfering_target_rows T p.1 p.2 hη)
    (fun p η hη => infinity_finite_interfering_sources hs hnot T p.1 p.2 hη)
    (fun r i => ‖block T i r‖) (fun r i j F => infinity_block_row_sum_le T i j r F)
  exact ⟨n, m, hn, hm, fun i j r s h => hsmall (r, s) (i, j) h.symm⟩

theorem infinity_pair_budget_hasSum (ε : ℝ) (i : ℕ) :
    HasSum (fun p : ℕ × ℕ => ε / (2 : ℝ) ^ (i + p.1 + p.2 + 5))
      (ε / (2 : ℝ) ^ (i + 3)) := by
  let g := fun n : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n
  have hg : HasSum g 1 := NormalizedSchauderBasis.hasSum_half_geometric
  have hprod : Summable (fun p : ℕ × ℕ => g p.1 * g p.2) := by
    apply (summable_prod_of_nonneg (fun p => by dsimp [g]; positivity)).mpr
    refine ⟨fun n => hg.summable.mul_left (g n), ?_⟩
    simpa only [tsum_mul_left, hg.tsum_eq, mul_one] using hg.summable
  convert ((hg.mul hg hprod).mul_left (ε / (2 : ℝ) ^ (i + 3))) using 1
  · funext p
    dsimp [g]
    simp only [div_eq_mul_inv, pow_add, inv_pow, one_mul]
    ring
  · simp

theorem infinity_small_cross_interaction (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ → ℕ) (m : ℕ → ℕ → ℕ), StrictMono n ∧ (∀ i, StrictMono (m i)) ∧
      ∀ i j, Summable (fun p : ℕ × ℕ => if p = (i, j) then 0 else
          ‖infinityEntry T (n i) (m i j) (n p.1) (m p.1 p.2)‖) ∧
        (∑' p : ℕ × ℕ, if p = (i, j) then 0 else
          ‖infinityEntry T (n i) (m i j) (n p.1) (m p.1 p.2)‖) <
            ε / (2 : ℝ) ^ (i + 1) := by
  classical
  obtain ⟨n, m, hn, hm, hsmall⟩ := infinity_asymmetric_selection hs hnot T hε
  refine ⟨n, m, hn, hm, ?_⟩
  intro i j
  let a := fun p : ℕ × ℕ => if p = (i, j) then 0 else
    ‖infinityEntry T (n i) (m i j) (n p.1) (m p.1 p.2)‖
  have ha (p : ℕ × ℕ) : 0 ≤ a p := by dsimp [a]; split_ifs <;> positivity
  have hbound (p : ℕ × ℕ) : a p ≤ ε / (2 : ℝ) ^ (i + p.1 + p.2 + 5) := by
    dsimp [a]
    split_ifs with hp
    · positivity
    · exact hsmall i j p.1 p.2 (Ne.symm hp)
  have hsum : Summable a := (infinity_pair_budget_hasSum ε i).summable.of_nonneg_of_le ha hbound
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ε / (2 : ℝ) ^ (i + 3) := by
      exact (hsum.tsum_le_tsum hbound (infinity_pair_budget_hasSum ε i).summable).trans_eq
        (infinity_pair_budget_hasSum ε i).tsum_eq
    _ < ε / (2 : ℝ) ^ (i + 1) := by
      apply div_lt_div_of_pos_left hε (by positivity)
      exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega)

end SchauderSum
end ThesisCommon
