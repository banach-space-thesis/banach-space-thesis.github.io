import ThesisCommon.Analysis.MatrixEntryNormBounds

/-! Phase alignment bounds bad source coefficients with a fixed target.
These are the two analytic obstructions used by finite Ramsey selection. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem matrix_column_coefficients_sum_le (p : BanachExponent)
    (hp : 0 < p.val.toReal) {N : ℕ}
    (T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    (I : Finset (Fin N)) (j k l : Fin N) :
    ∑ i ∈ I, ‖matrixEntry p k l (T (matrixUnit p i j))‖ ≤
      ‖T‖ * (I.card : ℝ) ^ (1 / p.val.toReal) := by
  choose a ha hphase using fun i : Fin N =>
    RCLike.exists_norm_eq_mul_self (matrixEntry p k l (T (matrixUnit p i j)))
  let u : FiniteMatrixBlock 𝕜 p N := ∑ i ∈ I, a i • matrixUnit p i j
  have heq : matrixEntry p k l (T u) =
      ((∑ i ∈ I, ‖matrixEntry p k l (T (matrixUnit p i j))‖ : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum]
    simp only [u, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => (hphase i).symm)
  calc
    _ = ‖matrixEntry p k l (T u)‖ := by
      rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖T u‖ := matrixEntry_norm_le p (T u) k l
    _ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
    _ = _ := by rw [norm_matrixUnit_column_sum p hp I a (fun i _ => ha i) j]

theorem matrix_row_coefficients_sum_le (p : BanachExponent)
    (hp : 1 < p.val.toReal) {N : ℕ}
    (T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    (J : Finset (Fin N)) (i k l : Fin N) :
    ∑ j ∈ J, ‖matrixEntry p k l (T (matrixUnit p i j))‖ ≤
      ‖T‖ * (J.card : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) := by
  classical
  by_cases hJ : J.Nonempty
  · choose a ha hphase using fun j : Fin N =>
      RCLike.exists_norm_eq_mul_self (matrixEntry p k l (T (matrixUnit p i j)))
    let u : FiniteMatrixBlock 𝕜 p N := ∑ j ∈ J, a j • matrixUnit p i j
    have heq : matrixEntry p k l (T u) =
        ((∑ j ∈ J, ‖matrixEntry p k l (T (matrixUnit p i j))‖ : ℝ) : 𝕜) := by
      rw [RCLike.ofReal_sum]
      simp only [u, map_sum, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl (fun j _ => (hphase j).symm)
    calc
      _ = ‖matrixEntry p k l (T u)‖ := by
        rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
      _ ≤ ‖T u‖ := matrixEntry_norm_le p (T u) k l
      _ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
      _ = _ := by rw [norm_matrixUnit_row_sum p hp J hJ a (fun j _ => ha j) i]
  · have hJe : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    rw [hJe]
    simp only [Finset.sum_empty]
    exact mul_nonneg (norm_nonneg T) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem matrix_bad_column_card_bound (p : BanachExponent)
    (hp : 0 < p.val.toReal) {N : ℕ}
    (T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    (I : Finset (Fin N)) (j k l : Fin N) {δ : ℝ}
    (hbad : ∀ i ∈ I, δ ≤ ‖matrixEntry p k l (T (matrixUnit p i j))‖) :
    δ * I.card ≤ ‖T‖ * (I.card : ℝ) ^ (1 / p.val.toReal) := by
  calc
    _ = ∑ _i ∈ I, δ := by simp [mul_comm]
    _ ≤ ∑ i ∈ I, ‖matrixEntry p k l (T (matrixUnit p i j))‖ := Finset.sum_le_sum hbad
    _ ≤ _ := matrix_column_coefficients_sum_le p hp T I j k l

theorem matrix_bad_row_card_bound (p : BanachExponent)
    (hp : 1 < p.val.toReal) {N : ℕ}
    (T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    (J : Finset (Fin N)) (i k l : Fin N) {δ : ℝ}
    (hbad : ∀ j ∈ J, δ ≤ ‖matrixEntry p k l (T (matrixUnit p i j))‖) :
    δ * J.card ≤ ‖T‖ * (J.card : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) := by
  calc
    _ = ∑ _j ∈ J, δ := by simp [mul_comm]
    _ ≤ ∑ j ∈ J, ‖matrixEntry p k l (T (matrixUnit p i j))‖ := Finset.sum_le_sum hbad
    _ ≤ _ := matrix_row_coefficients_sum_le p hp T J i k l

end ThesisCommon
