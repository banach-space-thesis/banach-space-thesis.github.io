import ThesisCommon.Analysis.GowersMaureyCoordinates
import ThesisCommon.Analysis.WienerConvolution
import ThesisCommon.Analysis.LpOneColumnsOperator

/-! Genuine absolutely summable Laurent-shift operators on the actual
Gowers--Maurey completion. This is the elementary forward construction
preceding Corollary 12 of Gowers--Maurey (arXiv:math/9407209, §4.2).
It does not assert the converse representation modulo strictly singular maps.
-/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def integerShift (D : ConstructionData 𝕜) : ℤ → ShiftSpace D →L[𝕜] ShiftSpace D
  | .ofNat n => completedSpread D 0 n
  | .negSucc n => completedSpread D (n + 1) 0

theorem norm_integerShift_le (D : ConstructionData 𝕜) (d : ℤ) :
    ‖integerShift D d‖ ≤ 1 := by
  cases d <;> exact norm_completedSpread_le D _ _

theorem matrixEntry_integerShift (D : ConstructionData 𝕜) (i j : ℕ) (d : ℤ) :
    matrixEntry D i j (integerShift D d) = if d = (i : ℤ) - j then 1 else 0 := by
  cases d with
  | ofNat n =>
    rw [matrixEntry_apply, integerShift, completedCoordinate_spread_basisVector]
    simp only [Nat.zero_le, Nat.sub_zero, true_and]
    have h : i = j + n ↔ (n : ℤ) = (i : ℤ) - j := by omega
    simp only [h, Int.ofNat_eq_coe]
  | negSucc n =>
    rw [matrixEntry_apply, integerShift, completedCoordinate_spread_basisVector]
    have h : n + 1 ≤ j ∧ i = j - (n + 1) + 0 ↔ Int.negSucc n = (i : ℤ) - j := by omega
    simp only [h]

/-- Norm-convergent Laurent synthesis on the literal Wiener sequence space. -/
def laurentOperator (D : ConstructionData 𝕜) :
    WienerSequences 𝕜 →L[𝕜] (ShiftSpace D →L[𝕜] ShiftSpace D) :=
  lpOneColumnsOperator (integerShift D) 1 zero_le_one (norm_integerShift_le D)

theorem laurentOperator_apply (D : ConstructionData 𝕜) (a : WienerSequences 𝕜) :
    laurentOperator D a = ∑' d : ℤ, a d • integerShift D d := rfl

theorem norm_laurentOperator_le (D : ConstructionData 𝕜) : ‖laurentOperator D‖ ≤ 1 :=
  norm_lpOneColumnsOperator_le _ _ _ _

theorem laurentOperator_summable_norm (D : ConstructionData 𝕜) (a : WienerSequences 𝕜) :
    Summable (fun d : ℤ => ‖a d • integerShift D d‖) := by
  apply (wiener_summable_norm a).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro d
  rw [norm_smul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (norm_integerShift_le D d) (norm_nonneg (a d))

@[simp] theorem laurentOperator_single (D : ConstructionData 𝕜) (d : ℤ) :
    laurentOperator D (lp.single 1 d 1) = integerShift D d := by
  rw [laurentOperator_apply, tsum_eq_single d]
  · simp
  · intro e he
    simp [lp.single_apply, he]

@[simp] theorem matrixEntry_laurentOperator (D : ConstructionData 𝕜)
    (a : WienerSequences 𝕜) (i j : ℕ) :
    matrixEntry D i j (laurentOperator D a) = a ((i : ℤ) - j) := by
  rw [laurentOperator_apply,
    (matrixEntry D i j).map_tsum (laurentOperator_summable_norm D a).of_norm,
    tsum_eq_single ((i : ℤ) - j)]
  · rw [map_smul, matrixEntry_integerShift]
    simp
  · intro d hd
    rw [map_smul, matrixEntry_integerShift, if_neg hd, smul_zero]

theorem laurentOperator_injective (D : ConstructionData 𝕜) :
    Function.Injective (laurentOperator D) := by
  intro a b h
  apply lp.ext
  funext d
  cases d with
  | ofNat n =>
    have heq := congrArg (matrixEntry D n 0) h
    rw [matrixEntry_laurentOperator, matrixEntry_laurentOperator] at heq
    simpa only [Nat.cast_zero, sub_zero, Int.ofNat_eq_coe] using heq
  | negSucc n =>
    have heq := congrArg (matrixEntry D 0 (n + 1)) h
    rw [matrixEntry_laurentOperator, matrixEntry_laurentOperator] at heq
    have hi : (0 : ℤ) - (n + 1 : ℕ) = Int.negSucc n := by omega
    simpa only [Nat.cast_zero, hi] using heq

end ThesisCommon.GowersMaurey
