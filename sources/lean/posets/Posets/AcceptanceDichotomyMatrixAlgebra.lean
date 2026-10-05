import Posets.AcceptanceAdmission

/-! Elementary matrix algebra needed for the scalar-shift acceptance test. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {M N : ScalarMatrix 𝕜}

theorem boundedRows_add (hM : HasBoundedRows 𝕜 M) (hN : HasBoundedRows 𝕜 N) :
    HasBoundedRows 𝕜 (M + N) := by
  have hs (k : ℕ) : Summable (fun n => ‖(M + N) k n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_add_le _ _)
      ((hM.1 k).add (hN.1 k))
  obtain ⟨C, hC⟩ := hM.2
  obtain ⟨D, hD⟩ := hN.2
  refine ⟨hs, C + D, fun k => ?_⟩
  calc
    (∑' n, ‖(M + N) k n‖) ≤ ∑' n, (‖M k n‖ + ‖N k n‖) :=
      (hs k).tsum_le_tsum (fun n => norm_add_le _ _) ((hM.1 k).add (hN.1 k))
    _ = (∑' n, ‖M k n‖) + ∑' n, ‖N k n‖ := (hM.1 k).tsum_add (hN.1 k)
    _ ≤ C + D := add_le_add (hC k) (hD k)

theorem boundedRows_neg (hM : HasBoundedRows 𝕜 M) : HasBoundedRows 𝕜 (-M) := by
  simpa only [HasBoundedRows, Pi.neg_apply, norm_neg] using hM

theorem boundedRows_sub (hM : HasBoundedRows 𝕜 M) (hN : HasBoundedRows 𝕜 N) :
    HasBoundedRows 𝕜 (M - N) := by
  simpa only [sub_eq_add_neg] using boundedRows_add hM (boundedRows_neg hN)

theorem matrixNorm_add_le (hM : HasBoundedRows 𝕜 M) (hN : HasBoundedRows 𝕜 N) :
    matrixNorm 𝕜 (M + N) ≤ matrixNorm 𝕜 M + matrixNorm 𝕜 N := by
  apply ciSup_le
  intro k
  calc
    (∑' n, ‖(M + N) k n‖) ≤ ∑' n, (‖M k n‖ + ‖N k n‖) :=
      ((boundedRows_add hM hN).1 k).tsum_le_tsum (fun n => norm_add_le _ _)
        ((hM.1 k).add (hN.1 k))
    _ = (∑' n, ‖M k n‖) + ∑' n, ‖N k n‖ := (hM.1 k).tsum_add (hN.1 k)
    _ ≤ matrixNorm 𝕜 M + matrixNorm 𝕜 N :=
      add_le_add (rowSum_le_matrixNorm M hM k) (rowSum_le_matrixNorm N hN k)

@[simp] theorem matrixTail_add (M N : ScalarMatrix 𝕜) (j : ℕ) :
    matrixTail 𝕜 (M + N) j = matrixTail 𝕜 M j + matrixTail 𝕜 N j := by
  funext k n
  by_cases h : j < n <;> simp [matrixTail, h]

@[simp] theorem matrixTail_neg (M : ScalarMatrix 𝕜) (j : ℕ) :
    matrixTail 𝕜 (-M) j = -matrixTail 𝕜 M j := by
  funext k n
  by_cases h : j < n <;> simp [matrixTail, h]

theorem compactMatrix_add (hM : IsCompactMatrix 𝕜 M) (hN : IsCompactMatrix 𝕜 N) :
    IsCompactMatrix 𝕜 (M + N) := by
  refine ⟨boundedRows_add hM.1 hN.1, ?_⟩
  have hlim : Tendsto (fun j => matrixNorm 𝕜 (matrixTail 𝕜 M j) +
      matrixNorm 𝕜 (matrixTail 𝕜 N j)) atTop (𝓝 0) := by simpa using hM.2.add hN.2
  apply squeeze_zero (fun j => matrixNorm_nonneg _
    (boundedRows_matrixTail _ (boundedRows_add hM.1 hN.1) j)) _ hlim
  intro j
  rw [matrixTail_add]
  exact matrixNorm_add_le (boundedRows_matrixTail _ hM.1 j) (boundedRows_matrixTail _ hN.1 j)

theorem compactMatrix_neg (hM : IsCompactMatrix 𝕜 M) : IsCompactMatrix 𝕜 (-M) := by
  refine ⟨boundedRows_neg hM.1, ?_⟩
  simpa only [matrixTail_neg, matrixNorm, Pi.neg_apply, norm_neg] using hM.2

theorem compactMatrix_sub (hM : IsCompactMatrix 𝕜 M) (hN : IsCompactMatrix 𝕜 N) :
    IsCompactMatrix 𝕜 (M - N) := by
  simpa only [sub_eq_add_neg] using compactMatrix_add hM (compactMatrix_neg hN)

/-- Entrywise absolute domination preserves the paper's compact-matrix condition. -/
theorem compactMatrix_of_domination (hN : IsCompactMatrix 𝕜 N)
    (h : ∀ k n, ‖M k n‖ ≤ ‖N k n‖) : IsCompactMatrix 𝕜 M := by
  refine ⟨boundedRows_of_domination hN.1 h, ?_⟩
  apply squeeze_zero (fun j => matrixNorm_nonneg _
    (boundedRows_matrixTail _ (boundedRows_of_domination hN.1 h) j)) _ hN.2
  intro j
  apply matrixNorm_le_of_domination (boundedRows_matrixTail _ hN.1 j)
  intro k n
  by_cases hn : j < n <;> simp [matrixTail, hn, h k n]

theorem boundedRows_identityMatrix : HasBoundedRows 𝕜 (identityMatrix 𝕜) := by
  constructor
  · intro k
    simp only [identityMatrix, apply_ite, norm_one, norm_zero]
    exact summable_of_ne_finset_zero (s := {k}) (by intro n hn; simp_all [eq_comm])
  · refine ⟨1, fun k => ?_⟩
    rw [tsum_eq_single k (fun n hn => by simp [identityMatrix, Ne.symm hn])]
    simp [identityMatrix]

theorem boundedRows_smul (a : 𝕜) (hM : HasBoundedRows 𝕜 M) : HasBoundedRows 𝕜 (a • M) := by
  constructor
  · intro k
    simpa only [Pi.smul_apply, norm_smul] using (hM.1 k).mul_left ‖a‖
  · obtain ⟨C, hC⟩ := hM.2
    refine ⟨‖a‖ * C, fun k => ?_⟩
    simp only [Pi.smul_apply, norm_smul, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hC k) (norm_nonneg a)

theorem boundedRows_scalarShift (hM : HasBoundedRows 𝕜 M) (a : 𝕜) :
    HasBoundedRows 𝕜 (M - a • identityMatrix 𝕜) :=
  boundedRows_sub hM (boundedRows_smul a boundedRows_identityMatrix)

theorem matrixAction_sub (hM : HasBoundedRows 𝕜 M) (hN : HasBoundedRows 𝕜 N)
    (f : ℕ →ᵇ 𝕜) (k : ℕ) :
    matrixAction 𝕜 (M - N) f k = matrixAction 𝕜 M f k - matrixAction 𝕜 N f k := by
  simp only [matrixAction, Pi.sub_apply, sub_mul]
  exact (summable_matrix_row M hM f k).tsum_sub (summable_matrix_row N hN f k)

@[simp] theorem matrixAction_scalarIdentity (a : 𝕜) (f : ℕ → 𝕜) (k : ℕ) :
    matrixAction 𝕜 (a • identityMatrix 𝕜) f k = a * f k := by
  unfold matrixAction
  rw [tsum_eq_single k (fun n hn => by simp [identityMatrix, Ne.symm hn])]
  simp [identityMatrix]

theorem matrixAction_scalarShift (hM : HasBoundedRows 𝕜 M) (a : 𝕜)
    (f : ℕ →ᵇ 𝕜) (k : ℕ) :
    matrixAction 𝕜 (M - a • identityMatrix 𝕜) f k = matrixAction 𝕜 M f k - a * f k := by
  rw [matrixAction_sub hM (boundedRows_smul a boundedRows_identityMatrix), matrixAction_scalarIdentity]

end Posets
