import ThesisCommon.Analysis.LpHaarEnumeration
import Mathlib.Algebra.BigOperators.Fin

/-! Exact finite-prefix decompositions for the natural Haar enumeration. -/

open scoped BigOperators
namespace ThesisCommon
variable {A : Type*} [AddCommMonoid A]

theorem lpHaar_sum_fin_prefix (f : ℕ → A) {k M : ℕ} (hk : k ≤ M) :
    (∑ j ∈ Finset.range k, f j) =
      ∑ j : Fin M, if j.val < k then f j.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then f j else 0) M,
    ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

theorem lpHaar_sum_power (f : ℕ → A) (n : ℕ) :
    (∑ i ∈ Finset.range (2 ^ n), f i) =
      f 0 + ∑ m ∈ Finset.range n, ∑ j : Fin (2 ^ m), f (2 ^ m + j.val) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by rw [pow_succ]; omega]
    rw [Finset.sum_range_add, ih, Finset.sum_range_succ]
    rw [Fin.sum_univ_eq_sum_range (fun j => f (2 ^ n + j)) (2 ^ n)]
    simp only [add_assoc]

theorem lpHaar_sum_level_prefix (f : ℕ → A) (n k : ℕ) :
    (∑ i ∈ Finset.range (2 ^ n + k), f i) =
      (f 0 + ∑ m ∈ Finset.range n, ∑ j : Fin (2 ^ m), f (2 ^ m + j.val)) +
        ∑ j ∈ Finset.range k, f (2 ^ n + j) := by
  rw [Finset.sum_range_add, lpHaar_sum_power]

theorem lpHaar_sum_prefix (f : ℕ → A) {N : ℕ} (hN : N ≠ 0) :
    (∑ i ∈ Finset.range N, f i) =
      (f 0 + ∑ m ∈ Finset.range N.log2, ∑ j : Fin (2 ^ m), f (2 ^ m + j.val)) +
        ∑ j ∈ Finset.range (N - 2 ^ N.log2), f (2 ^ N.log2 + j) := by
  have h := lpHaar_sum_level_prefix f N.log2 (N - 2 ^ N.log2)
  rwa [Nat.add_sub_of_le (lpHaar_pow_log2_le hN)] at h

theorem lpHaar_sum_decoded_prefix (f : Option LpHaarTreeIndex → A) {N : ℕ}
    (hN : N ≠ 0) :
    (∑ i ∈ Finset.range N, f (lpHaarDecode i)) =
      (f none + ∑ m ∈ Finset.range N.log2, ∑ j : Fin (2 ^ m), f (some ⟨m, j⟩)) +
        ∑ j ∈ Finset.range (N - 2 ^ N.log2), f (lpHaarDecode (2 ^ N.log2 + j)) := by
  rw [lpHaar_sum_prefix _ hN]
  simp only [lpHaarDecode_zero, lpHaarDecode_index]

theorem lpHaar_sum_decoded_prefix_fin (f : Option LpHaarTreeIndex → A) {N : ℕ}
    (hN : N ≠ 0) :
    (∑ i ∈ Finset.range N, f (lpHaarDecode i)) =
      (f none + ∑ m ∈ Finset.range N.log2, ∑ j : Fin (2 ^ m), f (some ⟨m, j⟩)) +
        ∑ j : Fin (2 ^ N.log2), if j.val < N - 2 ^ N.log2 then
          f (some ⟨N.log2, j⟩) else 0 := by
  rw [lpHaar_sum_decoded_prefix f hN]
  rw [lpHaar_sum_fin_prefix _ (lpHaar_remainder_lt N).le]
  simp only [lpHaarDecode_index]

end ThesisCommon
