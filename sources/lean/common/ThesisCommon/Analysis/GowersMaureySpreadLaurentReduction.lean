import ThesisCommon.Analysis.GowersMaureySeminormCoordinateKernel
import ThesisCommon.Analysis.GowersMaureyLaurentSeminorm
import ThesisCommon.Analysis.GowersMaureySpreadWeakDecay

/-! Actual tail spreads and their Laurent representatives differ only
on finitely many input coordinates. The same is proved for every finite
linear combination, giving the source's reduction from the spread algebra
to Laurent operators in the block seminorm. -/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem completedSpread_basis_tail_eq_integerShift (D : ConstructionData 𝕜)
    (m n j : ℕ) (hj : m ≤ j) :
    completedSpread D m n (basisVector D j) = integerShift D ((n : ℤ)-m) (basisVector D j) := by
  rw [completedSpread_basisVector, if_pos hj]
  by_cases hmn : m ≤ n
  · have he : (n : ℤ)-m = Int.ofNat (n-m) := by
      change (n : ℤ)-m = ((n-m : ℕ) : ℤ)
      omega
    rw [he, integerShift, completedSpread_basisVector, if_pos (Nat.zero_le _)]
    congr 1
    omega
  · have he : (n : ℤ)-m = Int.negSucc (m-n-1) := by omega
    rw [he, integerShift, completedSpread_basisVector, if_pos (by omega : m-n-1+1 ≤ j)]
    congr 1
    omega

theorem spaceOperatorSeminorm_spread_sub_integerShift (D : ConstructionData 𝕜) (m n : ℕ) :
    spaceOperatorSeminorm D (completedSpread D m n - integerShift D ((n : ℤ)-m)) = 0 := by
  apply spaceOperatorSeminorm_eq_zero_of_basis_tail D _ m
  intro j hj
  rw [ContinuousLinearMap.sub_apply, completedSpread_basis_tail_eq_integerShift D m n j (by omega),
    sub_self]

theorem laurentOperator_single_scalar (D : ConstructionData 𝕜) (d : ℤ) (c : 𝕜) :
    laurentOperator D (lp.single 1 d c) = c • integerShift D d := by
  have he : lp.single 1 d c = c • (lp.single 1 d 1 : WienerSequences 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using lp.single_smul
      (E := fun _ : ℤ => 𝕜) (1 : ℝ≥0∞) d c (1 : 𝕜)
  rw [he, map_smul, laurentOperator_single]

theorem spaceOperatorSeminorm_finite_spreads_sub_laurent
    (D : ConstructionData 𝕜) (s : Finset (ℕ×ℕ)) (c : ℕ×ℕ → 𝕜) :
    spaceOperatorSeminorm D ((∑ z ∈ s, c z • completedSpread D z.1 z.2) -
      laurentOperator D (∑ z ∈ s, lp.single 1 ((z.2 : ℤ)-z.1) (c z))) = 0 := by
  classical
  apply spaceOperatorSeminorm_eq_zero_of_basis_tail D _ (s.sup Prod.fst)
  intro j hj
  simp only [ContinuousLinearMap.sub_apply, map_sum, ContinuousLinearMap.sum_apply,
    laurentOperator_single_scalar, ContinuousLinearMap.smul_apply]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro z hz
  rw [completedSpread_basis_tail_eq_integerShift D z.1 z.2 j
    ((Finset.le_sup (f := Prod.fst) hz).trans hj.le)]

theorem spaceOperatorSeminorm_eq_of_sub_eq_zero (D : ConstructionData 𝕜)
    {S T : ShiftSpace D →L[𝕜] ShiftSpace D}
    (h : spaceOperatorSeminorm D (S-T) = 0) :
    spaceOperatorSeminorm D S = spaceOperatorSeminorm D T := by
  apply le_antisymm
  · have hh := map_add_le_add (spaceOperatorSeminorm D) (S-T) T
    simpa only [sub_add_cancel, h, zero_add] using hh
  · have hn : spaceOperatorSeminorm D (T-S) = 0 := by
      rw [← neg_sub S T, map_neg_eq_map, h]
    have hh := map_add_le_add (spaceOperatorSeminorm D) (T-S) S
    simpa only [sub_add_cancel, hn, zero_add] using hh

theorem spaceOperatorSeminorm_finite_spreads (D : ConstructionData 𝕜)
    (s : Finset (ℕ×ℕ)) (c : ℕ×ℕ → 𝕜) :
    spaceOperatorSeminorm D (∑ z ∈ s, c z • completedSpread D z.1 z.2) =
      ‖(∑ z ∈ s, lp.single 1 ((z.2 : ℤ)-z.1) (c z) : WienerSequences 𝕜)‖ := by
  rw [spaceOperatorSeminorm_eq_of_sub_eq_zero D
    (spaceOperatorSeminorm_finite_spreads_sub_laurent D s c)]
  exact spaceOperatorSeminorm_laurentOperator D _

end ThesisCommon.GowersMaurey
