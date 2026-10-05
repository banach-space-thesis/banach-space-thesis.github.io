import ThesisCommon.Analysis.MatrixCoefficientSums
import ThesisCommon.Analysis.MatrixPowerGrowth
import ThesisCommon.Combinatorics.MatrixRamseySelection

/-! The good-slice hypothesis in the Ramsey argument follows from actual
finite-matrix coefficient estimates. Natural indices are extended by zero. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def matrixNatCoefficient (p : BanachExponent) {N : ℕ}
    (T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    (i j k l : ℕ) : 𝕜 :=
  if h : i < N ∧ j < N ∧ k < N ∧ l < N then
    matrixEntry p ⟨k, h.2.2.1⟩ ⟨l, h.2.2.2⟩ (T (matrixUnit p ⟨i, h.1⟩ ⟨j, h.2.1⟩))
  else 0

@[simp] theorem matrixNatCoefficient_fin (p : BanachExponent) {N : ℕ}
    (T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    (i j k l : Fin N) :
    matrixNatCoefficient p T i j k l = matrixEntry p k l (T (matrixUnit p i j)) := by
  simp [matrixNatCoefficient, i.isLt, j.isLt, k.isLt, l.isLt]

theorem matrixNatCoefficient_norm_le (p : BanachExponent) {N : ℕ}
    (T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    (i j k l : ℕ) : ‖matrixNatCoefficient p T i j k l‖ ≤ ‖T‖ := by
  unfold matrixNatCoefficient
  split_ifs with h
  · exact (matrixEntry_norm_le p _ _ _).trans (by
      simpa only [norm_matrixUnit, mul_one] using T.le_opNorm (matrixUnit p ⟨i,h.1⟩ ⟨j,h.2.1⟩))
  · simpa only [norm_zero] using norm_nonneg T

theorem matrix_good_slices_of_power_bounds (p : BanachExponent) (hp : 1 < p.val.toReal)
    {N m : ℕ} (T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    {K δ : ℝ} (hT : ‖T‖ ≤ K)
    (hcol : K * (m : ℝ) ^ (1 / p.val.toReal) < δ * m)
    (hrow : K * (m : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) < δ * m) :
    MatrixGoodSlices (fun i j k l => ‖matrixNatCoefficient p T i j k l‖)
      δ m (Finset.range N : Set ℕ) := by
  classical
  constructor
  · intro j hj k hk l hl g hg
    have hj' : j < N := Finset.mem_range.mp hj
    have hk' : k < N := Finset.mem_range.mp hk
    have hl' : l < N := Finset.mem_range.mp hl
    have hg' (r : Fin m) : g r < N := Finset.mem_range.mp (hg ⟨r,rfl⟩)
    let f : Fin m ↪ Fin N := ⟨fun r => ⟨g r, hg' r⟩,
      fun r s h => g.injective (congrArg Fin.val h)⟩
    let I := Finset.univ.image f
    have hcard : I.card = m := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
    by_contra! hbad
    have h := matrix_bad_column_card_bound p (lt_trans zero_lt_one hp) T I
      ⟨j,hj'⟩ ⟨k,hk'⟩ ⟨l,hl'⟩ (δ := δ) (by
        intro i hi
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
        simpa [matrixNatCoefficient, hj', hk', hl', hg', f] using hbad r)
    rw [hcard] at h
    have hTK := mul_le_mul_of_nonneg_right hT
      (Real.rpow_nonneg (Nat.cast_nonneg m) (1 / p.val.toReal))
    exact (not_lt_of_ge (h.trans hTK)) hcol
  · intro i hi k hk l hl g hg
    have hi' : i < N := Finset.mem_range.mp hi
    have hk' : k < N := Finset.mem_range.mp hk
    have hl' : l < N := Finset.mem_range.mp hl
    have hg' (r : Fin m) : g r < N := Finset.mem_range.mp (hg ⟨r,rfl⟩)
    let f : Fin m ↪ Fin N := ⟨fun r => ⟨g r, hg' r⟩,
      fun r s h => g.injective (congrArg Fin.val h)⟩
    let J := Finset.univ.image f
    have hcard : J.card = m := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
    by_contra! hbad
    have h := matrix_bad_row_card_bound p hp T J
      ⟨i,hi'⟩ ⟨k,hk'⟩ ⟨l,hl'⟩ (δ := δ) (by
        intro j hj
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hj
        simpa [matrixNatCoefficient, hi', hk', hl', hg', f] using hbad r)
    rw [hcard] at h
    have hTK := mul_le_mul_of_nonneg_right hT
      (Real.rpow_nonneg (Nat.cast_nonneg m) (1 / (p.val.toReal / (p.val.toReal - 1))))
    exact (not_lt_of_ge (h.trans hTK)) hrow

end ThesisCommon

