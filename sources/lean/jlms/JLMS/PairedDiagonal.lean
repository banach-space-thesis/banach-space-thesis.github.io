import JLMS.PairedNormingOperator
import JLMS.CZeroMultiplier
import JLMS.CZeroMatrixNorm

/-!
# Positive paired diagonals and their matrix errors

Aligned norming functionals have positive real diagonal values. Pairing
retains their average, which remains bounded below. The reciprocal multiplier
is an exact inverse; summable off-diagonal column bounds control the error
in operator norm.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def pairedRealDiagonal (R : cZero 𝕜 →L[𝕜] X) (φ : ℕ → (X →L[𝕜] 𝕜))
    (s : ℕ → ℕ) (i : ℕ) : ℝ :=
  (RCLike.re (φ (s (2 * i)) (R (cZeroUnit 𝕜 (s (2 * i))))) +
    RCLike.re (φ (s (2 * i + 1)) (R (cZeroUnit 𝕜 (s (2 * i + 1)))))) / 2

theorem pairedRealDiagonal_lower (R : cZero 𝕜 →L[𝕜] X)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (s : ℕ → ℕ) {γ : ℝ}
    (hdiag : ∀ n, γ ≤ RCLike.re (φ n (R (cZeroUnit 𝕜 n)))) (i : ℕ) :
    γ ≤ pairedRealDiagonal R φ s i := by
  dsimp [pairedRealDiagonal]
  linarith [hdiag (s (2 * i)), hdiag (s (2 * i + 1))]

theorem pairedRealDiagonal_upper (R : cZero 𝕜 →L[𝕜] X)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (hφ : ∀ n, ‖φ n‖ ≤ 1) (s : ℕ → ℕ) (i : ℕ) :
    pairedRealDiagonal R φ s i ≤ ‖R‖ := by
  have hb (n : ℕ) : RCLike.re (φ n (R (cZeroUnit 𝕜 n))) ≤ ‖R‖ := by
    calc
      _ ≤ ‖φ n (R (cZeroUnit 𝕜 n))‖ := RCLike.re_le_norm _
      _ ≤ ‖φ n‖ * ‖R (cZeroUnit 𝕜 n)‖ := (φ n).le_opNorm _
      _ ≤ 1 * ‖R (cZeroUnit 𝕜 n)‖ := mul_le_mul_of_nonneg_right (hφ n) (norm_nonneg _)
      _ ≤ ‖R‖ := by
        simp only [one_mul]
        exact (R.le_opNorm _).trans (by
          simpa using mul_le_mul_of_nonneg_left (cZero_subsequenceUnits_norm_le id n) (norm_nonneg R))
  dsimp [pairedRealDiagonal]
  linarith [hb (s (2 * i)), hb (s (2 * i + 1))]

theorem pairedRealDiagonal_cast (R : cZero 𝕜 →L[𝕜] X)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (s : ℕ → ℕ)
    (halign : ∀ n, φ n (R (cZeroUnit 𝕜 n)) =
      (RCLike.re (φ n (R (cZeroUnit 𝕜 n))) : 𝕜)) (i : ℕ) :
    (pairedRealDiagonal R φ s i : 𝕜) =
      pairedDiagonalCoefficient (fun i j => φ (s i) (R (cZeroUnit 𝕜 (s j)))) i := by
  conv_rhs => rw [pairedDiagonalCoefficient, halign (s (2 * i)), halign (s (2 * i + 1))]
  simp only [pairedRealDiagonal, RCLike.ofReal_div, RCLike.ofReal_add,
    RCLike.ofReal_ofNat, RCLike.ofReal_one]
  ring

theorem cZeroReciprocalMultiplier_leftInverse (d : ℕ → ℝ) {γ C : ℝ}
    (hγ : 0 < γ) (hd : ∀ n, γ ≤ d n) (hC : 0 ≤ C)
    (hbound : ∀ n, ‖(d n : 𝕜)‖ ≤ C) :
    (cZeroReciprocalMultiplier (𝕜 := 𝕜) d hγ hd).comp
      (cZeroMultiplier (fun n => (d n : 𝕜)) C hC hbound) =
        ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  apply ContinuousLinearMap.ext
  intro a
  ext n
  have hn : (d n : 𝕜) ≠ 0 := by
    exact_mod_cast (hγ.trans_le (hd n)).ne'
  change (d n : 𝕜)⁻¹ * ((d n : 𝕜) * a n) = a n
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem pairedNormingOperator_error (R : cZero 𝕜 →L[𝕜] X)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (hφ : ∀ n, ‖φ n‖ ≤ 1) (ψ : X →L[𝕜] 𝕜)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (ht : ∀ x, Tendsto (fun n => φ (s n) x) atTop (𝓝 (ψ x)))
    (halign : ∀ n, φ n (R (cZeroUnit 𝕜 n)) =
      (RCLike.re (φ n (R (cZeroUnit 𝕜 n))) : 𝕜))
    (D : cZero 𝕜 →L[𝕜] cZero 𝕜)
    (hD : ∀ a i, D a i = (pairedRealDiagonal R φ s i : 𝕜) * a i)
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    (hoff : ∀ i j, i ≠ j → ‖φ (s i) (R (cZeroUnit 𝕜 (s j)))‖ ≤ w (j / 2)) :
    ‖D - ((pairedNormingOperator (φ ∘ s) (fun n => hφ (s n)) ψ ht).comp R).comp
      (cZeroPairInsertion s hs)‖ ≤ ∑' j, 2 * w j := by
  apply norm_cZero_operator_le_column_budget _ (fun j => 2 * w j)
    (fun j => mul_nonneg (by norm_num) (hw j)) (hsum.mul_left 2)
  intro i j
  simp only [ContinuousLinearMap.sub_apply, ZeroAtInftyContinuousMap.sub_apply,
    hD, cZeroUnit_apply, pairedNormingOperator_matrix]
  have heq : (pairedRealDiagonal R φ s i : 𝕜) * (if i = j then 1 else 0) =
      if j = i then pairedDiagonalCoefficient (fun i j => φ (s i) (R (cZeroUnit 𝕜 (s j)))) i else 0 := by
    by_cases hij : i = j
    · simp [hij, pairedRealDiagonal_cast R φ s halign]
    · simp [hij, Ne.symm hij]
  rw [heq, norm_sub_rev]
  exact norm_pairedMatrix_error_le _ w hw hoff i j

end JLMS
