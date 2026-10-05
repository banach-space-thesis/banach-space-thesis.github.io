import ThesisCommon.Analysis.EllOneColumns

/-! The finite-family pigeonhole argument for mixed ell_1 sums. The
candidate output rows and retained source columns may be different infinite
sets. Repeating the one-family choice after removing any finite set proves
there are infinitely many admissible rows, and finite induction preserves
the conditions already imposed.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

theorem bounded_columns_small_row_between (w : ℕ → ℕ → ℝ) {C ε : ℝ}
    (hbound : ∀ n (F : Finset ℕ), ∑ s ∈ F, w s n ≤ C) (hε : 0 < ε)
    {A M : Set ℕ} (hA : A.Infinite) (hM : M.Infinite) :
    ∃ s ∈ A, {m ∈ M | w s m < ε}.Infinite := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have hlarge : C < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  let a : Fin N ↪ ℕ := (Fin.valEmbedding.trans (hA.natEmbedding A)).trans
    (Function.Embedding.subtype A)
  let e : ℕ ↪ ℕ := (hM.natEmbedding M).trans (Function.Embedding.subtype M)
  have hs (m : ℕ) : ∃ i : Fin N, w (a i) (e m) < ε := by
    by_contra hn
    push_neg at hn
    have hlower : (N : ℝ) * ε ≤ ∑ i : Fin N, w (a i) (e m) := by
      calc
        _ = ∑ _i : Fin N, ε := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hn i)
    have hupper := hbound (e m) (Finset.univ.map a)
    rw [Finset.sum_map] at hupper
    exact (not_le_of_gt hlarge) (hlower.trans hupper)
  choose i hi using hs
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber i
  have hj' : (i ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
  refine ⟨a j, (hA.natEmbedding A j).property, ?_⟩
  apply Set.Infinite.mono (s := e '' (i ⁻¹' {j}))
  · rintro m ⟨k, hk, rfl⟩
    have heq : i k = j := hk
    exact ⟨(hM.natEmbedding M k).property, by simpa only [heq] using hi k⟩
  · exact (Set.infinite_image_iff e.injective.injOn).mpr hj'

theorem bounded_columns_good_rows_infinite (w : ℕ → ℕ → ℝ) {C ε : ℝ}
    (hbound : ∀ n (F : Finset ℕ), ∑ s ∈ F, w s n ≤ C) (hε : 0 < ε)
    {A M : Set ℕ} (hA : A.Infinite) (hM : M.Infinite) :
    {s ∈ A | {m ∈ M | w s m < ε}.Infinite}.Infinite := by
  classical
  by_contra hfin
  have hd := hA.diff (Set.not_infinite.mp hfin)
  obtain ⟨s, hs, hgood⟩ := bounded_columns_small_row_between w hbound hε hd hM
  exact hs.2 ⟨hs.1, hgood⟩

/-- One candidate works for every member of a finite family. Thresholds
may differ across the family, and the admissible candidates remain infinite. -/
theorem bounded_columns_simultaneous_small_rows {ι : Type*}
    (w : ι → ℕ → ℕ → ℝ) (C ε : ι → ℝ)
    (hbound : ∀ k n (F : Finset ℕ), ∑ s ∈ F, w k s n ≤ C k)
    (hε : ∀ k, 0 < ε k) (K : Finset ι) (M : ι → Set ℕ)
    {A : Set ℕ} (hA : A.Infinite) (hM : ∀ k ∈ K, (M k).Infinite) :
    {s ∈ A | ∀ k ∈ K, {m ∈ M k | w k s m < ε k}.Infinite}.Infinite := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa using hA
  | @insert k K hk ih =>
    have hprev := ih (fun i hi => hM i (Finset.mem_insert_of_mem hi))
    have hnext := bounded_columns_good_rows_infinite (w k) (hbound k) (hε k)
      hprev (hM k (Finset.mem_insert_self _ _))
    apply Set.Infinite.mono _ hnext
    rintro s ⟨⟨hsA, hsK⟩, hsk⟩
    refine ⟨hsA, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hsk
    · exact hsK i hi

end ThesisCommon
