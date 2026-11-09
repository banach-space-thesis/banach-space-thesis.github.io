import ThesisCommon.Analysis.CotypeUpperTriangular
import ThesisCommon.Analysis.SequenceOffDiagonal
import ThesisCommon.Analysis.SequenceEntryAlgebra

/-! UPFP Proposition 5.3, with the actual diagonal part of the compressed
operator. The proof applies the lower reduction, then the upper entry bound,
and adds the two errors. The whole-operator prefix identities handle ℓ∞.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Finite cotype gives the manuscript's diagonal reduction on ℓ∞(X). -/
theorem HasFiniteCotype.infinity_diagonal_reduction (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧
      ‖((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e) -
        lpDiagonalPart (((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e))‖ < ε := by
  obtain ⟨e, L, he, hclose, hL⟩ := h.infinity_lower_triangular T (half_pos hε)
  let S := ((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e)
  obtain ⟨f, hf, hupper⟩ := h.infinity_upper_triangular L (half_pos hε)
  let U := ((lpRestrict ∞ f).comp S).comp (lpExtend ∞ f)
  let K := ((lpRestrict ∞ f).comp L).comp (lpExtend ∞ f)
  have hK : IsLpLowerPart K K := hL.compression f hf
  have hrows : ∀ k, (∑ j ∈ Finset.range k, ‖lpEntry K k j‖) ≤ ε / 2 := by
    intro k
    simp only [K, lpEntry_compression]
    exact (hupper k).le
  have hoff : ‖K - lpDiagonalPart K‖ ≤ ε / 2 :=
    hK.infinity_norm_sub_diagonal_le (half_pos hε).le hrows
  have hfirst : ‖U - K‖ < ε / 2 := by
    have hid : U - K = ((lpRestrict ∞ f).comp (S - L)).comp (lpExtend ∞ f) := by
      ext x k
      rfl
    rw [hid]
    exact (norm_contractive_compression (S - L) (lpRestrict ∞ f) (lpExtend ∞ f)
      (norm_lpRestrict_le f) (norm_lpExtend_le f)).trans_lt hclose
  have hdiag : lpDiagonalPart U = lpDiagonalPart K := by
    ext x k
    change lpEntry U k k (x k) = lpEntry K k k (x k)
    have hd : lpEntry U k k = lpEntry K k k := by
      simp only [U, K, lpEntry_compression]
      exact (hL.diagonal_entry (f k)).symm
    rw [hd]
  have hU : U = ((lpRestrict ∞ (f.trans e)).comp T).comp (lpExtend ∞ (f.trans e)) :=
    lpCompression_composition T e f
  refine ⟨f.trans e, he.comp hf, ?_⟩
  rw [← hU]
  calc
    ‖U - lpDiagonalPart U‖ ≤ ‖U - K‖ + ‖K - lpDiagonalPart U‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (U - K) (K - lpDiagonalPart U)
    _ = ‖U - K‖ + ‖K - lpDiagonalPart K‖ := by rw [hdiag]
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hfirst hoff
    _ = ε := by ring

/-- Finite cotype gives the same actual diagonal reduction on c₀(X). -/
theorem HasFiniteCotype.cZero_diagonal_reduction (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] CZeroSum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧
      ‖((cZeroRestrict e).comp T).comp (cZeroExtend e) -
        cZeroDiagonalPart (((cZeroRestrict e).comp T).comp (cZeroExtend e))‖ < ε := by
  obtain ⟨e, L, he, hclose, hL⟩ := h.cZero_lower_triangular T (half_pos hε)
  let S := ((cZeroRestrict e).comp T).comp (cZeroExtend e)
  obtain ⟨f, hf, hupper⟩ := h.cZero_upper_triangular L (half_pos hε)
  let U := ((cZeroRestrict f).comp S).comp (cZeroExtend f)
  let K := ((cZeroRestrict f).comp L).comp (cZeroExtend f)
  have hK : IsCZeroLowerPart K K := hL.compression f hf
  have hrows : ∀ k, (∑ j ∈ Finset.range k, ‖cZeroEntry K k j‖) ≤ ε / 2 := by
    intro k
    simp only [K, cZeroEntry_compression]
    exact (hupper k).le
  have hoff : ‖K - cZeroDiagonalPart K‖ ≤ ε / 2 :=
    hK.norm_sub_diagonal_le (half_pos hε).le hrows
  have hfirst : ‖U - K‖ < ε / 2 := by
    have hid : U - K = ((cZeroRestrict f).comp (S - L)).comp (cZeroExtend f) := by
      ext x k
      rfl
    rw [hid]
    exact (norm_contractive_compression (S - L) (cZeroRestrict f) (cZeroExtend f)
      (norm_cZeroRestrict_le f) (norm_cZeroExtend_le f)).trans_lt hclose
  have hdiag : cZeroDiagonalPart U = cZeroDiagonalPart K := by
    ext x k
    change cZeroEntry U k k (x k) = cZeroEntry K k k (x k)
    have hd : cZeroEntry U k k = cZeroEntry K k k := by
      simp only [U, K, cZeroEntry_compression]
      exact (hL.diagonal_entry (f k)).symm
    rw [hd]
  have hU : U = ((cZeroRestrict (f.trans e)).comp T).comp (cZeroExtend (f.trans e)) :=
    cZeroCompression_composition T e f
  refine ⟨f.trans e, he.comp hf, ?_⟩
  rw [← hU]
  calc
    ‖U - cZeroDiagonalPart U‖ ≤ ‖U - K‖ + ‖K - cZeroDiagonalPart U‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (U - K) (K - cZeroDiagonalPart U)
    _ = ‖U - K‖ + ‖K - cZeroDiagonalPart K‖ := by rw [hdiag]
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hfirst hoff
    _ = ε := by ring

end ThesisCommon
