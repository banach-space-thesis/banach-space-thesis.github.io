import Posets.CZeroContinuousAmplificationColumns
import Posets.MatrixNorm

/-! Every scalar operator on a c₀ sum has countable row and column supports.
The row estimate uses finite phase tests over real or complex scalars. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {I : Type}

def cZeroSumScalarMatrix
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (i j : I) : 𝕜 := T (JLMS.CZeroSum.single j 1) i

theorem cZeroSum_scalar_finite_sum_norm_le (s : Finset I) (a : I → 𝕜)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ i ∈ s, ‖a i‖ ≤ M) :
    ‖∑ i ∈ s, JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun _ : I => 𝕜) i (a i)‖ ≤ M := by
  classical
  apply JLMS.CZeroSum.norm_le hM
  intro j
  rw [JLMS.CZeroSum.sum_apply]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single j]
    · simpa using ha j hj
    · intro k hk hkj
      exact JLMS.CZeroSum.single_apply_ne k _ hkj.symm
    · exact fun h => (h hj).elim
  · rw [Finset.sum_eq_zero (fun k hk => JLMS.CZeroSum.single_apply_ne
      (𝕜 := 𝕜) (E := fun _ : I => 𝕜) k (a k) (fun he : j = k => hj (he.symm ▸ hk))), norm_zero]
    exact hM

theorem cZeroSumScalarMatrix_finite_row_bound
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (i : I) (s : Finset I) : ∑ j ∈ s, ‖cZeroSumScalarMatrix T i j‖ ≤ ‖T‖ := by
  classical
  let a (j : I) := normingPhase (cZeroSumScalarMatrix T i j)
  let x : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) := ∑ j ∈ s, JLMS.CZeroSum.single j (a j)
  have hx : ‖x‖ ≤ 1 := cZeroSum_scalar_finite_sum_norm_le s a zero_le_one
    (fun _ _ => norm_normingPhase_le _)
  have he : T x i = ((∑ j ∈ s, ‖cZeroSumScalarMatrix T i j‖ : ℝ) : 𝕜) := by
    change T (∑ j ∈ s, JLMS.CZeroSum.single j (a j)) i = _
    simp only [map_sum, JLMS.CZeroSum.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [cZeroScalarSingle_smul j (a j), map_smul, JLMS.CZeroSum.smul_apply]
    change a j * cZeroSumScalarMatrix T i j = _
    rw [mul_comm]
    exact mul_normingPhase _
  calc
    (∑ j ∈ s, ‖cZeroSumScalarMatrix T i j‖) = ‖T x i‖ := by
      rw [he, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖T x‖ := (T x).norm_apply_le_norm i
    _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    _ ≤ ‖T‖ := by nlinarith [norm_nonneg T]

theorem cZeroSumScalarMatrix_countable_row
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (i : I) : {j | cZeroSumScalarMatrix T i j ≠ 0}.Countable := by
  have hs : Summable (fun j => ‖cZeroSumScalarMatrix T i j‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) (cZeroSumScalarMatrix_finite_row_bound T i)
  simpa only [Function.support, norm_ne_zero_iff] using hs.countable_support

theorem cZeroSum_countable_support (x : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) :
    {i | x i ≠ 0}.Countable := by
  have hc : (⋃ n : ℕ, {i | (1 : ℝ) / (n + 1) ≤ ‖x i‖}).Countable :=
    Set.countable_iUnion (fun n => (x.finite_norm_ge (by positivity : (0 : ℝ) < 1 / (n + 1))).countable)
  apply hc.mono
  intro i hi
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hi)
  exact mem_iUnion.mpr ⟨n, hn.le⟩

theorem cZeroSumScalarMatrix_countable_column
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (j : I) : {i | cZeroSumScalarMatrix T i j ≠ 0}.Countable :=
  cZeroSum_countable_support _

def cZeroSumMatrixForbidden
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (i : I) : Set I :=
  {i} ∪ {j | cZeroSumScalarMatrix T i j ≠ 0} ∪ {j | cZeroSumScalarMatrix T j i ≠ 0}

theorem cZeroSumMatrixForbidden_countable
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (i : I) : (cZeroSumMatrixForbidden T i).Countable :=
  ((countable_singleton i).union (cZeroSumScalarMatrix_countable_row T i)).union
    (cZeroSumScalarMatrix_countable_column T i)

theorem cZeroSumMatrixForbidden_self
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (i : I) : i ∈ cZeroSumMatrixForbidden T i := Or.inl (Or.inl rfl)

theorem cZeroSumMatrixForbidden_symm
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (i j : I) (h : i ∈ cZeroSumMatrixForbidden T j) : j ∈ cZeroSumMatrixForbidden T i := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h.symm)
  · exact Or.inr h
  · exact Or.inl (Or.inr h)

end Posets
