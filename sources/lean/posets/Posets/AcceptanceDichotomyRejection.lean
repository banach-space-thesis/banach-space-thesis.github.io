import Posets.AcceptanceDichotomyScalarBorel

/-! Rejection witnesses when the off-diagonal restriction is compact. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

/-- Convergence is preserved by uniform approximation on cofinite tails,
even when the approximating limit depends on the tail. -/
theorem exists_tendsto_along_of_tail_uniform_approximation (A : Set ℕ)
    (f : ℕ → 𝕜) (g : ℕ → ℕ → 𝕜)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ j : ℕ, ∀ k ∈ A, j < k → dist (g j k) (f k) < ε)
    (hconv : ∀ j : ℕ, ∃ a : 𝕜, Tendsto (g j) (Along (A ∩ Set.Ioi j)) (𝓝 a)) :
    ∃ a : 𝕜, Tendsto f (Along A) (𝓝 a) := by
  apply (exists_tendsto_along_iff_cauchyAlongNat A f).mpr
  intro i
  let ε : ℝ := 1 / ((i : ℝ) + 1)
  have hε : 0 < ε / 4 := by dsimp [ε]; positivity
  obtain ⟨j, hj⟩ := happrox (ε / 4) hε
  obtain ⟨a, ha⟩ := hconv j
  have he := Metric.tendsto_nhds.mp ha (ε / 4) hε
  rw [Along, Nat.cofinite_eq_atTop, eventually_inf_principal, eventually_atTop] at he
  obtain ⟨N, hN⟩ := he
  refine ⟨max N (j + 1), fun m n hm hn hmA hnA => ?_⟩
  have hmj : j < m := lt_of_lt_of_le (Nat.lt_succ_self j) ((le_max_right _ _).trans hm)
  have hnj : j < n := lt_of_lt_of_le (Nat.lt_succ_self j) ((le_max_right _ _).trans hn)
  have hm₁ := hj m hmA hmj
  have hn₁ := hj n hnA hnj
  have hm₂ := hN m ((le_max_left _ _).trans hm) ⟨hmA, hmj⟩
  have hn₂ := hN n ((le_max_left _ _).trans hn) ⟨hnA, hnj⟩
  have ht₁ := dist_triangle (f m) (g j m) (f n)
  have ht₂ := dist_triangle (g j m) a (f n)
  have ht₃ := dist_triangle a (g j n) (f n)
  rw [dist_comm (f m) (g j m)] at ht₁
  rw [dist_comm a (g j n)] at ht₃
  change dist (f m) (f n) < ε
  linarith

theorem infinite_of_not_exists_tendsto_along (A : Set ℕ) (f : ℕ → 𝕜)
    (h : ¬ ∃ a : 𝕜, Tendsto f (Along A) (𝓝 a)) : A.Infinite := by
  by_contra hA
  have hb : Along A = ⊥ := by
    apply not_neBot.mp
    simpa only [Along, cofinite_inf_principal_neBot_iff] using hA
  exact h ⟨0, by rw [hb]; exact tendsto_bot⟩

/-- On a tail of A, the error from the diagonal is bounded by the compact
off-diagonal tail norm. -/
theorem matrixAction_indicator_tail_sub_diagonal_bound (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) (A : Set ℕ) (j k : ℕ) (hk : k ∈ A ∩ Set.Ioi j) :
    ‖matrixAction 𝕜 M (indicator 𝕜 (A ∩ Set.Ioi j)) k - M k k‖ ≤
      matrixNorm 𝕜 (matrixTail 𝕜 (matrixRestriction 𝕜 (matrixOffDiagonal M) A A) j) := by
  let B := A ∩ Set.Ioi j
  let f : ℕ →ᵇ 𝕜 := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (indicator 𝕜 B) 1 (fun n => by by_cases hn : n ∈ B <;> simp [indicator, hn])
  have hf : ‖f‖ ≤ 1 := BoundedContinuousFunction.norm_le (by norm_num) |>.mpr
    (fun n => by by_cases hn : n ∈ B <;> simp [f, indicator, hn])
  let N := matrixTail 𝕜 (matrixRestriction 𝕜 (matrixOffDiagonal M) A A) j
  have hN : HasBoundedRows 𝕜 N := boundedRows_matrixTail _
    (boundedRows_matrixRestriction _ (boundedRows_matrixOffDiagonal hM) A A) j
  have heq : matrixAction 𝕜 M f k = M k k + matrixAction 𝕜 N f k := by
    have hsum := (summable_matrix_row (matrixDiagonal M) (boundedRows_matrixDiagonal hM) f k).tsum_add
      (summable_matrix_row N hN f k)
    have hpoint (n : ℕ) : M k n * f n = matrixDiagonal M k n * f n + N k n * f n := by
      by_cases hn : n ∈ B
      · have hnA := hn.1
        have hnj : j < n := hn.2
        by_cases hkn : k = n
        · subst n; simp [f, indicator, hn, matrixDiagonal, N, matrixTail, matrixRestriction,
            matrixOffDiagonal]
        · simp [f, indicator, hn, matrixDiagonal, N, matrixTail, matrixRestriction,
            matrixOffDiagonal, hkn, hk.1, hnA, hnj]
      · simp [f, indicator, hn]
    have hd : matrixAction 𝕜 (matrixDiagonal M) f k = M k k := by
      rw [matrixAction_diagonal]
      simp [f, indicator, B, hk]
    calc
      matrixAction 𝕜 M f k = matrixAction 𝕜 (matrixDiagonal M) f k + matrixAction 𝕜 N f k := by
        change (∑' n, M k n * f n) = _
        simp_rw [hpoint]
        exact hsum
      _ = M k k + matrixAction 𝕜 N f k := by rw [hd]
  change ‖matrixAction 𝕜 M f k - M k k‖ ≤ matrixNorm 𝕜 N
  rw [heq, add_sub_cancel_left]
  exact (matrixAction_bound N hN f k).trans (by
    simpa using mul_le_mul_of_nonneg_left hf (matrixNorm_nonneg N hN))

/-- If no scalar shift is accepted while the off-diagonal restriction is
compact, a cofinite tail of the set already rejects the matrix. -/
theorem exists_rejecting_subset_of_compact_offDiagonal (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) (A : Set ℕ)
    (hoff : AcceptsPair 𝕜 A A (matrixOffDiagonal M))
    (hno : ¬ ∃ a : 𝕜, AcceptsPair 𝕜 A A (M - a • identityMatrix 𝕜)) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ Rejects 𝕜 B B M := by
  have hd : ¬ ∃ a : 𝕜, Tendsto (fun k => M k k) (Along A) (𝓝 a) := by
    intro h
    exact hno ((exists_acceptsPair_scalarShift_iff hM A).mpr ⟨hoff, h⟩)
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ j : ℕ, ∀ k ∈ A, j < k →
      dist (matrixAction 𝕜 M (indicator 𝕜 (A ∩ Set.Ioi j)) k) (M k k) < ε := by
    intro ε hε
    obtain ⟨j, hj⟩ := (hoff.2.eventually (gt_mem_nhds hε)).exists
    refine ⟨j, fun k hk hkj => ?_⟩
    rw [dist_eq_norm]
    exact (matrixAction_indicator_tail_sub_diagonal_bound M hM A j k ⟨hk, hkj⟩).trans_lt hj
  have hbad : ¬ ∀ j : ℕ, ∃ a : 𝕜,
      Tendsto (matrixAction 𝕜 M (indicator 𝕜 (A ∩ Set.Ioi j)))
        (Along (A ∩ Set.Ioi j)) (𝓝 a) := by
    intro h
    exact hd (exists_tendsto_along_of_tail_uniform_approximation A (fun k => M k k)
      (fun j => matrixAction 𝕜 M (indicator 𝕜 (A ∩ Set.Ioi j))) happrox h)
  push_neg at hbad
  obtain ⟨j, hj⟩ := hbad
  have hn : ¬ ∃ a : 𝕜, Tendsto (matrixAction 𝕜 M (indicator 𝕜 (A ∩ Set.Ioi j)))
      (Along (A ∩ Set.Ioi j)) (𝓝 a) := by simpa only [not_exists] using hj
  exact ⟨A ∩ Set.Ioi j, Set.inter_subset_left,
    infinite_of_not_exists_tendsto_along _ _ hn, hn⟩

end Posets
