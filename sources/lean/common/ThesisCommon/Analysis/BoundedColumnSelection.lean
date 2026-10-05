import ThesisCommon.Analysis.EllOneColumns
import ThesisCommon.Analysis.PositiveMatrix

/-! Nested-set selection for nonnegative matrices with uniformly bounded
column sums. This is the shared scalar ell_1 / transposed ell_infinity
interference argument. The retained set can be prescribed in advance.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

theorem bounded_columns_two_sided_selection (w : ℕ → ℕ → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {C : ℝ}
    (hbound : ∀ j (F : Finset ℕ), ∑ i ∈ F, w i j ≤ C)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) {M : Set ℕ} (hM : M.Infinite) :
    ∃ f : ℕ ↪ ℕ, StrictMono f ∧ (∀ k, f k ∈ M) ∧
      (∀ i j, i < j → w (f i) (f j) < δ i) ∧
      (∀ j (F : Finset ℕ), (∀ i ∈ F, j < i) → ∑ i ∈ F, w (f i) (f j) < δ j) := by
  classical
  have step : ∀ k (A : Set ℕ), A.Infinite → ∃ n ∈ A, ∃ B : Set ℕ,
      B.Infinite ∧ B ⊆ A ∧ (∀ m ∈ B, n < m) ∧
      ((∀ m ∈ B, w n m < δ k) ∧
        ∀ F : Finset ℕ, (∀ m ∈ F, m ∈ B) → ∑ m ∈ F, w m n < δ k) := by
    intro k A hA
    obtain ⟨n, hn, B, hB, hBA, hBn, hBw⟩ := bounded_columns_small_row w hbound (hδ k) hA
    obtain ⟨N, hN⟩ := summable_small_tail (summable_of_sum_le (fun i => hw i n) (hbound n)) (hδ k)
    refine ⟨n, hn, {m ∈ B | N < m}, infinite_above hB N,
      fun m hm => hBA hm.1, fun m hm => hBn m hm.1,
      (fun m hm => hBw m hm.1), ?_⟩
    intro F hF
    exact hN F (fun m hm => (hF m hm).2.le)
  obtain ⟨f, A, hzero, _, hmem, hnest, _, hf, hQ, htail⟩ := infinite_fusion
    (fun k n B => (∀ m ∈ B, w n m < δ k) ∧
      ∀ F : Finset ℕ, (∀ m ∈ F, m ∈ B) → ∑ m ∈ F, w m n < δ k) hM step
  refine ⟨⟨f, hf.injective⟩, hf, ?_, ?_, ?_⟩
  · intro k
    rw [← hzero]
    exact (antitone_nat_of_succ_le hnest) (Nat.zero_le k) (hmem k)
  · intro i j hij
    exact (hQ i).1 (f j) (htail i j hij)
  · intro j F hF
    have hh := (hQ j).2 (F.image f) (by
      intro m hm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      exact htail j i (hF i hi))
    simpa only [Finset.sum_image, hf.injective.injOn] using hh

theorem bounded_columns_small_off_diagonal (w : ℕ → ℕ → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {C : ℝ}
    (hbound : ∀ j (F : Finset ℕ), ∑ i ∈ F, w i j ≤ C)
    {M : Set ℕ} (hM : M.Infinite) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℕ ↪ ℕ, StrictMono f ∧ (∀ k, f k ∈ M) ∧ ∀ k,
      Summable (fun j => if j = k then 0 else w (f j) (f k)) ∧
      (∑' j, if j = k then 0 else w (f j) (f k)) < ε := by
  classical
  let δ := fun k => (ε / 4) * (1 / 2 : ℝ) ^ k
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hsum : HasSum δ (ε / 2) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (ε / 4) using 1
    norm_num
    ring
  obtain ⟨f, hf, hfM, hfuture, htail⟩ := bounded_columns_two_sided_selection w hw hbound δ hδ hM
  refine ⟨f, hf, hfM, ?_⟩
  intro k
  let v := fun j => if j = k then 0 else w (f j) (f k)
  have hv (j : ℕ) : 0 ≤ v j := by dsimp [v]; split_ifs; exact le_rfl; exact hw _ _
  have hfinite (F : Finset ℕ) : ∑ j ∈ F, v j ≤ 3 * ε / 4 := by
    let past := F.filter (fun j => j < k)
    let rest := F.filter (fun j => ¬ j < k)
    have hpast : ∑ j ∈ past, v j ≤ ε / 2 := by
      calc
        _ ≤ ∑ j ∈ past, δ j := Finset.sum_le_sum (by
          intro j hj
          have hjk := (Finset.mem_filter.mp hj).2
          rw [show v j = w (f j) (f k) from if_neg (ne_of_lt hjk)]
          exact (hfuture j k hjk).le)
        _ ≤ ∑' j, δ j := hsum.summable.sum_le_tsum _ (fun j _ => (hδ j).le)
        _ = ε / 2 := hsum.tsum_eq
    have hrest : ∑ j ∈ rest, v j < δ k := by
      let later := rest.erase k
      have heq : ∑ j ∈ rest, v j = ∑ j ∈ later, w (f j) (f k) := by
        calc
          _ = ∑ j ∈ later, v j := (Finset.sum_erase rest (by simp [v])).symm
          _ = _ := Finset.sum_congr rfl (fun j hj => if_neg (Finset.mem_erase.mp hj).1)
      rw [heq]
      apply htail k later
      intro j hj
      have hne := (Finset.mem_erase.mp hj).1
      have hnlt := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
      omega
    have hδle : δ k ≤ ε / 4 := mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun j => j < k) v
    change (∑ j ∈ past, v j) + (∑ j ∈ rest, v j) = _ at hsplit
    linarith
  have hs : Summable v := summable_of_sum_le hv hfinite
  exact ⟨hs, (hs.tsum_le_of_sum_le hfinite).trans_lt (by linarith)⟩

end ThesisCommon
