import ThesisCommon.Analysis.CZeroColumnOperators
import ThesisCommon.Analysis.CZeroSchauderBasis
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! Successive finite blocks attaining a common lower bound for every tail
restriction of an actual c₀ operator. This is the constructive block step
in the nondistortion argument. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def cZeroTailEmbedding (p : ℕ) : ℕ ↪ ℕ := ⟨fun n => p+n, by intro i j hij; dsimp at hij; omega⟩

theorem exists_cZero_finite_tail_norming_vector
    (V : CZeroSum 𝕜 →L[𝕜] E) (p : ℕ) {r : ℝ}
    (hr : r < ‖V.comp (cZeroExtend (cZeroTailEmbedding p))‖) :
    ∃ q : ℕ, ∃ x : CZeroSum 𝕜, p < q ∧ ‖x‖ ≤ 1 ∧
      (∀ i, i < p ∨ q ≤ i → x i = 0) ∧ r < ‖V x‖ := by
  classical
  let J := cZeroExtend (𝕜 := 𝕜) (X := 𝕜) (cZeroTailEmbedding p)
  obtain ⟨y, hy, hVy⟩ := (V.comp J).exists_lt_apply_of_lt_opNorm hr
  let z (N : ℕ) := ∑ n ∈ Finset.range N, y n • cZeroSingle n (1 : 𝕜)
  have ht : Tendsto (fun N => ‖V (J (z N))‖) atTop (𝓝 ‖V (J y)‖) :=
    ((V.continuous.comp J.continuous).tendsto y |>.comp (cZero_finite_singles_tendsto y)).norm
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (Ioi_mem_nhds hVy))
  have hz : ‖z N‖ ≤ ‖y‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg y)).2
    intro i
    change ‖(∑ n ∈ Finset.range N, y n • cZeroSingle n (1 : 𝕜)) i‖ ≤ ‖y‖
    rw [cZero_finite_singles_apply]
    split_ifs
    · exact BoundedContinuousFunction.norm_coe_le_norm y.toBCF i
    · simp
  refine ⟨p+N+1, J (z N), by omega, ?_, ?_, hN N le_rfl⟩
  · exact (norm_cZeroInsert_le (cZeroTailEmbedding p) (z N)).trans (hz.trans hy.le)
  · intro i hi
    change Function.extend (cZeroTailEmbedding p) (z N) 0 i = 0
    by_cases hpi : p ≤ i
    · have heq : cZeroTailEmbedding p (i-p) = i := by dsimp [cZeroTailEmbedding]; omega
      rw [← heq, Function.Injective.extend_apply (cZeroTailEmbedding p).injective]
      change (∑ n ∈ Finset.range N, y n • cZeroSingle n (1 : 𝕜)) (i-p) = 0
      rw [cZero_finite_singles_apply, if_neg]
      simp only [Finset.mem_range]
      omega
    · apply Function.extend_apply' _ _ _
      rintro ⟨j, hj⟩
      change p+j=i at hj
      omega

theorem exists_cZero_successive_norming_blocks (V : CZeroSum 𝕜 →L[𝕜] E) {r : ℝ}
    (hr : ∀ p, r < ‖V.comp (cZeroExtend (cZeroTailEmbedding p))‖) :
    ∃ x : ℕ → CZeroSum 𝕜, (∀ n, ‖x n‖ ≤ 1) ∧
      (∀ i j, i ≠ j → ∀ k, x i k = 0 ∨ x j k = 0) ∧
      ∀ n, r < ‖V (x n)‖ := by
  classical
  choose q x hq hx hs hV using fun p => exists_cZero_finite_tail_norming_vector V p (hr p)
  let p : ℕ → ℕ := fun n => q^[n] 0
  have hp : ∀ n, p (n+1) = q (p n) := fun n => Function.iterate_succ_apply' q n 0
  have hpm : StrictMono p := strictMono_nat_of_lt_succ (fun n => by rw [hp]; exact hq _)
  refine ⟨fun n => x (p n), fun n => hx _, ?_, fun n => hV _⟩
  intro i j hij k
  rcases lt_or_gt_of_ne hij with hij | hji
  · by_cases hk : k < q (p i)
    · right
      apply hs (p j) k
      left
      have hle := hpm.monotone (Nat.succ_le_of_lt hij)
      rw [hp] at hle
      omega
    · exact Or.inl (hs (p i) k (Or.inr (le_of_not_gt hk)))
  · by_cases hk : k < q (p j)
    · left
      apply hs (p i) k
      left
      have hle := hpm.monotone (Nat.succ_le_of_lt hji)
      rw [hp] at hle
      omega
    · exact Or.inr (hs (p j) k (Or.inr (le_of_not_gt hk)))

theorem cZero_disjoint_finiteColumnBound (x : ℕ → CZeroSum 𝕜)
    (hx : ∀ n, ‖x n‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ k, x i k = 0 ∨ x j k = 0) :
    CZeroFiniteColumnBound
      (fun n => (ContinuousLinearMap.id 𝕜 𝕜).smulRight (x n)) 1 := by
  classical
  intro s a b hb ha
  simp only [one_mul]
  apply (BoundedContinuousFunction.norm_le hb).2
  intro k
  change ‖cZeroCoordinate (𝕜 := 𝕜) k
    (∑ n ∈ s, (ContinuousLinearMap.id 𝕜 𝕜).smulRight (x n) (a n))‖ ≤ b
  simp only [map_sum, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    map_smul, cZeroCoordinate_apply, smul_eq_mul]
  by_cases hh : ∃ i ∈ s, x i k ≠ 0
  · obtain ⟨i, hi, hne⟩ := hh
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [norm_mul]
      exact (mul_le_mul (ha i hi)
        ((BoundedContinuousFunction.norm_coe_le_norm (x i).toBCF k).trans (hx i))
        (norm_nonneg _) hb).trans_eq (mul_one b)
    · intro j hj hji
      rw [(hdis i j hji.symm k).resolve_left hne, mul_zero]
  · push_neg at hh
    rw [Finset.sum_eq_zero (fun i hi => by rw [hh i hi, mul_zero]), norm_zero]
    exact hb

theorem exists_cZero_norming_block_operator (V : CZeroSum 𝕜 →L[𝕜] E) {r : ℝ}
    (hr : ∀ p, r < ‖V.comp (cZeroExtend (cZeroTailEmbedding p))‖) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ‖A‖ ≤ 1 ∧
      ∀ n, r < ‖V (A (cZeroSingle n 1))‖ := by
  obtain ⟨x, hx, hdis, hV⟩ := exists_cZero_successive_norming_blocks V hr
  let F (n : ℕ) := (ContinuousLinearMap.id 𝕜 𝕜).smulRight (x n)
  let A := cZeroColumns F 1 zero_le_one (cZero_disjoint_finiteColumnBound x hx hdis)
  refine ⟨A, norm_cZeroColumns_le .., ?_⟩
  intro n
  have heq : A (cZeroSingle n 1) = x n := by
    rw [show A = cZeroColumns F 1 zero_le_one (cZero_disjoint_finiteColumnBound x hx hdis) from rfl,
      cZeroColumns_single]
    simp [F]
  rw [heq]
  exact hV n

end ThesisCommon

