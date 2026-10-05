import Posets.AcceptanceDichotomyMatrixAlgebra

/-! The diagonal criterion underlying scalar-shift acceptance. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {M : ScalarMatrix 𝕜}

def matrixDiagonal (M : ScalarMatrix 𝕜) : ScalarMatrix 𝕜 :=
  fun k n => if k = n then M k k else 0

def matrixOffDiagonal (M : ScalarMatrix 𝕜) : ScalarMatrix 𝕜 :=
  fun k n => if k = n then 0 else M k n

theorem norm_matrixDiagonal_le (M : ScalarMatrix 𝕜) (k n : ℕ) :
    ‖matrixDiagonal M k n‖ ≤ ‖M k n‖ := by
  by_cases h : k = n
  · subst n; simp [matrixDiagonal]
  · simp [matrixDiagonal, h]

theorem norm_matrixOffDiagonal_le (M : ScalarMatrix 𝕜) (k n : ℕ) :
    ‖matrixOffDiagonal M k n‖ ≤ ‖M k n‖ := by
  by_cases h : k = n <;> simp [matrixOffDiagonal, h]

theorem boundedRows_matrixDiagonal (hM : HasBoundedRows 𝕜 M) :
    HasBoundedRows 𝕜 (matrixDiagonal M) := boundedRows_of_domination hM (norm_matrixDiagonal_le M)

theorem boundedRows_matrixOffDiagonal (hM : HasBoundedRows 𝕜 M) :
    HasBoundedRows 𝕜 (matrixOffDiagonal M) := boundedRows_of_domination hM (norm_matrixOffDiagonal_le M)

theorem compactMatrix_diagonal (hM : IsCompactMatrix 𝕜 M) :
    IsCompactMatrix 𝕜 (matrixDiagonal M) := compactMatrix_of_domination hM (norm_matrixDiagonal_le M)

theorem compactMatrix_offDiagonal (hM : IsCompactMatrix 𝕜 M) :
    IsCompactMatrix 𝕜 (matrixOffDiagonal M) := compactMatrix_of_domination hM (norm_matrixOffDiagonal_le M)

@[simp] theorem matrixDiagonal_add_offDiagonal (M : ScalarMatrix 𝕜) :
    matrixDiagonal M + matrixOffDiagonal M = M := by
  funext k n
  by_cases h : k = n
  · subst n; simp [matrixDiagonal, matrixOffDiagonal]
  · simp [matrixDiagonal, matrixOffDiagonal, h]

@[simp] theorem matrixAction_diagonal (M : ScalarMatrix 𝕜) (f : ℕ → 𝕜) (k : ℕ) :
    matrixAction 𝕜 (matrixDiagonal M) f k = M k k * f k := by
  unfold matrixAction
  rw [tsum_eq_single k (fun n hn => by simp [matrixDiagonal, Ne.symm hn])]
  simp [matrixDiagonal]

theorem compactMatrix_diagonal_tendsto (hM : IsCompactMatrix 𝕜 M) :
    Tendsto (fun k => M k k) atTop (𝓝 0) := by
  have hc (n : ℕ) : Tendsto (fun k => matrixDiagonal M k n) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with k hk
    simp [matrixDiagonal, ne_of_gt hk]
  have h := compactMatrix_action_tendsto_zero (matrixDiagonal M) (compactMatrix_diagonal hM)
    atTop hc (BoundedContinuousFunction.const ℕ (1 : 𝕜))
  change Tendsto (fun k => matrixAction 𝕜 (matrixDiagonal M)
    (BoundedContinuousFunction.const ℕ (1 : 𝕜)) k) atTop (𝓝 0) at h
  simpa only [matrixAction_diagonal, BoundedContinuousFunction.const_apply, mul_one] using h

theorem rowSum_tail_matrixDiagonal (M : ScalarMatrix 𝕜) (j k : ℕ) :
    (∑' n, ‖matrixTail 𝕜 (matrixDiagonal M) j k n‖) = if j < k then ‖M k k‖ else 0 := by
  rw [tsum_eq_single k (fun n hn => by simp [matrixTail, matrixDiagonal, Ne.symm hn])]
  by_cases h : j < k <;> simp [matrixTail, matrixDiagonal, h]

theorem compactMatrix_diagonal_of_tendsto (hM : HasBoundedRows 𝕜 M)
    (hd : Tendsto (fun k => M k k) atTop (𝓝 0)) : IsCompactMatrix 𝕜 (matrixDiagonal M) := by
  refine ⟨boundedRows_matrixDiagonal hM, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro r hr
    exact Eventually.of_forall (fun j => hr.trans_le (matrixNorm_nonneg _
      (boundedRows_matrixTail _ (boundedRows_matrixDiagonal hM) j)))
  · intro ε hε
    have hn : Tendsto (fun k => ‖M k k‖) atTop (𝓝 0) := by simpa using hd.norm
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hn).2 (ε / 2) (by positivity))
    filter_upwards [eventually_ge_atTop N] with j hj
    have hb : matrixNorm 𝕜 (matrixTail 𝕜 (matrixDiagonal M) j) ≤ ε / 2 := by
      apply ciSup_le
      intro k
      rw [rowSum_tail_matrixDiagonal]
      split_ifs with hk
      · exact (hN k (hj.trans (le_of_lt hk))).le
      · positivity
    linarith

theorem compactMatrix_diagonal_iff (hM : HasBoundedRows 𝕜 M) :
    IsCompactMatrix 𝕜 (matrixDiagonal M) ↔ Tendsto (fun k => M k k) atTop (𝓝 0) := by
  constructor
  · intro hd
    simpa only [matrixDiagonal, ite_true] using compactMatrix_diagonal_tendsto hd
  · exact compactMatrix_diagonal_of_tendsto hM

/-- A compact matrix is exactly one with compact off-diagonal part and vanishing diagonal. -/
theorem compactMatrix_iff_offDiagonal_and_diagonal (hM : HasBoundedRows 𝕜 M) :
    IsCompactMatrix 𝕜 M ↔ IsCompactMatrix 𝕜 (matrixOffDiagonal M) ∧
      Tendsto (fun k => M k k) atTop (𝓝 0) := by
  constructor
  · exact fun h => ⟨compactMatrix_offDiagonal h, compactMatrix_diagonal_tendsto h⟩
  · rintro ⟨ho, hd⟩
    simpa only [matrixDiagonal_add_offDiagonal] using
      compactMatrix_add (compactMatrix_diagonal_of_tendsto hM hd) ho

theorem tendsto_indicator_along_iff (A : Set ℕ) (f : ℕ → 𝕜) :
    Tendsto (A.indicator f) atTop (𝓝 0) ↔ Tendsto f (Along A) (𝓝 0) := by
  constructor
  · intro h
    have hr : Tendsto (A.indicator f) (Along A) (𝓝 0) := h.mono_left (by
      rw [Along, Nat.cofinite_eq_atTop]
      exact inf_le_left)
    apply hr.congr'
    filter_upwards [eventually_mem_along A] with n hn
    exact Set.indicator_of_mem hn f
  · intro h
    have hr : Tendsto f (atTop ⊓ Filter.principal A) (𝓝 0) := by
      simpa only [Along, Nat.cofinite_eq_atTop] using h
    exact hr.piecewise (g := fun _ => 0) tendsto_const_nhds

@[simp] theorem matrixOffDiagonal_scalarShift (M : ScalarMatrix 𝕜) (a : 𝕜) :
    matrixOffDiagonal (M - a • identityMatrix 𝕜) = matrixOffDiagonal M := by
  funext k n
  by_cases h : k = n <;> simp [matrixOffDiagonal, identityMatrix, h]

@[simp] theorem matrixOffDiagonal_restriction (M : ScalarMatrix 𝕜) (A B : Set ℕ) :
    matrixOffDiagonal (matrixRestriction 𝕜 M A B) = matrixRestriction 𝕜 (matrixOffDiagonal M) A B := by
  funext k n
  by_cases h : k = n <;> by_cases h' : k ∈ B ∧ n ∈ A <;>
    simp [matrixOffDiagonal, matrixRestriction, h, h']

/-- The scalar in a compact scalar-shift restriction is precisely the diagonal limit. -/
theorem acceptsPair_scalarShift_iff (hM : HasBoundedRows 𝕜 M) (A : Set ℕ) (a : 𝕜) :
    AcceptsPair 𝕜 A A (M - a • identityMatrix 𝕜) ↔
      AcceptsPair 𝕜 A A (matrixOffDiagonal M) ∧ Tendsto (fun k => M k k) (Along A) (𝓝 a) := by
  change IsCompactMatrix 𝕜 (matrixRestriction 𝕜 (M - a • identityMatrix 𝕜) A A) ↔ _
  rw [compactMatrix_iff_offDiagonal_and_diagonal
    (boundedRows_matrixRestriction _ (boundedRows_scalarShift hM a) A A),
    matrixOffDiagonal_restriction, matrixOffDiagonal_scalarShift]
  have heq : (fun k => matrixRestriction 𝕜 (M - a • identityMatrix 𝕜) A A k k) =
      A.indicator (fun k => M k k - a) := by
    funext k
    by_cases hk : k ∈ A <;> simp [matrixRestriction, identityMatrix, hk]
  rw [heq, tendsto_indicator_along_iff]
  constructor
  · rintro ⟨ho, hd⟩
    exact ⟨ho, by simpa only [sub_add_cancel, zero_add] using hd.add_const a⟩
  · rintro ⟨ho, hd⟩
    exact ⟨ho, by simpa only [sub_self] using hd.sub_const a⟩

theorem acceptsPair_scalarShift_unique (hM : HasBoundedRows 𝕜 M) {A : Set ℕ} (hA : A.Infinite)
    {a b : 𝕜} (ha : AcceptsPair 𝕜 A A (M - a • identityMatrix 𝕜))
    (hb : AcceptsPair 𝕜 A A (M - b • identityMatrix 𝕜)) : a = b := by
  letI : NeBot (Along A) := hA.cofinite_inf_principal_neBot
  exact tendsto_nhds_unique ((acceptsPair_scalarShift_iff hM A a).mp ha).2
    ((acceptsPair_scalarShift_iff hM A b).mp hb).2

theorem exists_acceptsPair_scalarShift_iff (hM : HasBoundedRows 𝕜 M) (A : Set ℕ) :
    (∃ a : 𝕜, AcceptsPair 𝕜 A A (M - a • identityMatrix 𝕜)) ↔
      AcceptsPair 𝕜 A A (matrixOffDiagonal M) ∧
        ∃ a : 𝕜, Tendsto (fun k => M k k) (Along A) (𝓝 a) := by
  simp only [acceptsPair_scalarShift_iff hM, exists_and_left]

end Posets
