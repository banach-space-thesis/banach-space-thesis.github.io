import ThesisCommon.Analysis.FiniteLpNormComparison
import ThesisCommon.Analysis.MatrixHilbertSchmidtBounds

/-! Changing the exponent of a finite matrix preserves its scalar entries
and Hilbert--Schmidt norm. The two coordinate maps give the exact dimension
factor N^|1/p-1/q| in the operator norm. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def matrixExponentChange (p q : BanachExponent) (hp : p.val ≠ ∞) (hq : q.val ≠ ∞)
    {N : ℕ} (A : FiniteMatrixBlock 𝕜 p N) : FiniteMatrixBlock 𝕜 q N :=
  (finiteLpChange (𝕜 := 𝕜) (N := N) p q hp hq).comp
    (A.comp (finiteLpChange (𝕜 := 𝕜) (N := N) q p hq hp))

theorem finiteLpChange_single (p q : BanachExponent) (hp : p.val ≠ ∞) (hq : q.val ≠ ∞)
    {N : ℕ} (j : Fin N) (a : 𝕜) :
    finiteLpChange (𝕜 := 𝕜) p q hp hq (lp.single p.val j a) = lp.single q.val j a := by
  apply lp.ext
  funext i
  simp only [finiteLpChange_apply, lp.single_apply, Pi.single_apply]

@[simp] theorem matrixEntry_exponentChange (p q : BanachExponent)
    (hp : p.val ≠ ∞) (hq : q.val ≠ ∞) {N : ℕ}
    (A : FiniteMatrixBlock 𝕜 p N) (i j : Fin N) :
    matrixEntry (𝕜 := 𝕜) q i j (matrixExponentChange (𝕜 := 𝕜) p q hp hq A) =
      matrixEntry (𝕜 := 𝕜) p i j A := by
  change A (finiteLpChange (𝕜 := 𝕜) q p hq hp (lp.single q.val j (1 : 𝕜))) i =
    A (lp.single p.val j (1 : 𝕜)) i
  exact congrArg (fun x : FiniteLpSpace 𝕜 p N => A x i)
    (finiteLpChange_single q p hq hp j (1 : 𝕜))

@[simp] theorem matrixHilbertSchmidtNorm_exponentChange (p q : BanachExponent)
    (hp : p.val ≠ ∞) (hq : q.val ≠ ∞) {N : ℕ} (A : FiniteMatrixBlock 𝕜 p N) :
    matrixHilbertSchmidtNorm (𝕜 := 𝕜) q (matrixExponentChange (𝕜 := 𝕜) p q hp hq A) =
      matrixHilbertSchmidtNorm (𝕜 := 𝕜) p A := by
  simp only [matrixHilbertSchmidtNorm, matrixEntry_exponentChange]

@[simp] theorem matrixExponentChange_inverse (p q : BanachExponent)
    (hp : p.val ≠ ∞) (hq : q.val ≠ ∞) {N : ℕ} (A : FiniteMatrixBlock 𝕜 p N) :
    matrixExponentChange (𝕜 := 𝕜) q p hq hp
      (matrixExponentChange (𝕜 := 𝕜) p q hp hq A) = A := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  rw [finiteMatrix_apply_eq_sum, finiteMatrix_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [matrixEntry_exponentChange, matrixEntry_exponentChange]

theorem norm_matrixExponentChange_le (p q : BanachExponent)
    (hp : p.val ≠ ∞) (hq : q.val ≠ ∞) {N : ℕ} (hN : 0 < N)
    (A : FiniteMatrixBlock 𝕜 p N) :
    ‖matrixExponentChange (𝕜 := 𝕜) p q hp hq A‖ ≤
      (N : ℝ) ^ |1 / p.val.toReal - 1 / q.val.toReal| * ‖A‖ := by
  let J := finiteLpChange (𝕜 := 𝕜) (N := N) p q hp hq
  let R := finiteLpChange (𝕜 := 𝕜) (N := N) q p hq hp
  let c := (N : ℝ) ^ max (1 / q.val.toReal - 1 / p.val.toReal) 0
  let d := (N : ℝ) ^ max (1 / p.val.toReal - 1 / q.val.toReal) 0
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hd : 0 ≤ d := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hJ : ‖J‖ ≤ c := norm_finiteLpChange_le (𝕜 := 𝕜) (N := N) p q hp hq
  have hR : ‖R‖ ≤ d := norm_finiteLpChange_le (𝕜 := 𝕜) (N := N) q p hq hp
  have hsum : max (1 / q.val.toReal - 1 / p.val.toReal) 0 +
      max (1 / p.val.toReal - 1 / q.val.toReal) 0 =
      |1 / p.val.toReal - 1 / q.val.toReal| := by
    by_cases h : 1 / p.val.toReal ≤ 1 / q.val.toReal
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h),
        abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · have h' := (le_of_not_ge h)
      rw [max_eq_right (sub_nonpos.mpr h'), max_eq_left (sub_nonneg.mpr h'),
        abs_of_nonneg (sub_nonneg.mpr h')]
      ring
  have hcd : c * d = (N : ℝ) ^ |1 / p.val.toReal - 1 / q.val.toReal| := by
    dsimp [c, d]
    rw [← Real.rpow_add (Nat.cast_pos.mpr hN), hsum]
  calc
    ‖matrixExponentChange (𝕜 := 𝕜) p q hp hq A‖ ≤ ‖J‖ * (‖A‖ * ‖R‖) :=
      (J.opNorm_comp_le (A.comp R)).trans
        (mul_le_mul_of_nonneg_left (A.opNorm_comp_le R) (norm_nonneg J))
    _ ≤ c * (‖A‖ * d) := mul_le_mul hJ
      (mul_le_mul_of_nonneg_left hR (norm_nonneg A))
      (mul_nonneg (norm_nonneg A) (norm_nonneg R)) hc
    _ = (c * d) * ‖A‖ := by ring
    _ = _ := by rw [hcd]

end ThesisCommon

