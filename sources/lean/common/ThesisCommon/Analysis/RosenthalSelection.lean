import ThesisCommon.Analysis.PositiveMatrix
import ThesisCommon.Analysis.FiniteHistory

/-! Rosenthal selection for absolutely summable rows, the form needed for
the atomic measures in Sigma Lemma 4.7. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon

theorem rosenthal_finite_sums (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 ≤ w n m)
    (hbound : ∀ n (F : Finset ℕ), ∑ m ∈ F, w n m ≤ 1)
    (C : Set ℕ) (hC : C.Infinite) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ (∀ n, r n ∈ C) ∧
      ∀ n (F : Finset ℕ), (∀ m ∈ F, m ∈ Set.range r ∧ m ≠ r n) →
        ∑ m ∈ F, w (r n) m ≤ 2 * (δ / 3) := by
  classical
  have hε : 0 < δ / 3 := by linarith
  obtain ⟨q, v, hq, hqC, hv, hvs, hlim⟩ := positive_matrix_cluster w hw hbound C hC
  obtain ⟨N, hN⟩ := summable_small_tail hvs hε
  have hrows (n : ℕ) : Summable (w n) := summable_of_sum_le (hw n) (hbound n)
  choose cut hcut using fun n => summable_small_tail (hrows n) hε
  let P : ℕ → Finset ℕ → Prop := fun n F =>
    (∀ m ∈ F, cut m ≤ n) ∧ ∑ m ∈ F, w n m < δ / 3
  have hnext (F : Finset ℕ) (hF : ∀ m ∈ F, m ∈ C ∩ Set.Ici N) :
      ∃ n ∈ C ∩ Set.Ici N, (∀ m ∈ F, m < n) ∧ P n F := by
    obtain ⟨n, hnC, hnN, hnF, hnsmall⟩ :=
      positive_matrix_next_row w v q hq C hqC hlim (δ / 3) N hN cut F
        (fun m hm => (hF m hm).2)
    exact ⟨n, ⟨hnC, hnN⟩, fun m hm => (hnF m hm).1,
      fun m hm => (hnF m hm).2, hnsmall⟩
  obtain ⟨r, hr, hrC, hrP⟩ := increasing_finite_history (C ∩ Set.Ici N) P hnext
  refine ⟨r, hr, fun n => (hrC n).1, ?_⟩
  intro n F hF
  let past := (Finset.range n).image r
  have hfirst : ∑ m ∈ F ∩ past, w (r n) m < δ / 3 := by
    have hle : ∑ m ∈ F ∩ past, w (r n) m ≤ ∑ m ∈ past, w (r n) m :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun m _ _ => hw _ _)
    exact hle.trans_lt (hrP n).2
  have hlast : ∑ m ∈ F \ past, w (r n) m < δ / 3 := by
    apply hcut (r n)
    intro m hm
    obtain ⟨hmF, hmPast⟩ := Finset.mem_sdiff.mp hm
    obtain ⟨⟨k, rfl⟩, hkn⟩ := hF m hmF
    have hnk : n < k := by
      by_contra h
      have hkn' : k ≤ n := le_of_not_gt h
      have hne : k ≠ n := fun h => hkn (congrArg r h)
      have hklt : k < n := lt_of_le_of_ne hkn' hne
      exact hmPast (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hklt, rfl⟩)
    exact (hrP k).1 (r n) (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hnk, rfl⟩)
  have hsum : (∑ m ∈ F \ past, w (r n) m) +
      (∑ m ∈ F ∩ past, w (r n) m) = ∑ m ∈ F, w (r n) m := by
    simpa using (Finset.sum_sdiff (f := w (r n)) (Finset.inter_subset_left : F ∩ past ⊆ F))
  linarith

/-- An infinite subset on which each selected row has arbitrarily small total
off-diagonal mass. No finite-additive measure assumption is used: these are
the countably additive atomic rows to which the paper applies Rosenthal. -/
theorem rosenthal_selection (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 ≤ w n m)
    (hbound : ∀ n (F : Finset ℕ), ∑ m ∈ F, w n m ≤ 1)
    (C : Set ℕ) (hC : C.Infinite) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : Set ℕ, J ⊆ C ∧ J.Infinite ∧
      ∀ n ∈ J, (∑' m : ↥(J \ {n}), w n m.val) < δ := by
  classical
  obtain ⟨r, hr, hrC, hsum⟩ := rosenthal_finite_sums w hw hbound C hC δ hδ
  refine ⟨Set.range r, ?_, Set.infinite_range_of_injective hr.injective, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact hrC n
  · rintro _ ⟨n, rfl⟩
    have hrow : Summable (w (r n)) := summable_of_sum_le (hw _) (hbound _)
    have hsub : Summable (fun m : ↥(Set.range r \ {r n}) => w (r n) m.val) := hrow.subtype _
    have hb : (∑' m : ↥(Set.range r \ {r n}), w (r n) m.val) ≤ 2 * (δ / 3) := by
      apply hsub.tsum_le_of_sum_le
      intro F
      have hF := hsum n (F.image Subtype.val) (by
        intro m hm
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
        exact ⟨x.property.1, x.property.2⟩)
      simpa only [Finset.sum_image, Subtype.val_injective.injOn] using hF
    linarith

end ThesisCommon
