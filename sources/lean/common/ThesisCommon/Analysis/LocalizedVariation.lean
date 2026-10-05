import ThesisCommon.Analysis.HaydonFinite

/-! The finite Haydon estimate with arbitrary, varying tests inside each
supporting set. This permits adjoining both halves of a cylinder at once. -/
noncomputable section
open Set
namespace ThesisCommon

theorem UnitCharge.sum_abs_diff_le_two {α : Type*} (μ ν : UnitCharge α) {n : ℕ}
    (A : Fin n → Set α) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ i, |μ (A i) - ν (A i)| ≤ 2 := by
  calc
    _ ≤ ∑ i, (|μ (A i)| + |ν (A i)|) := Finset.sum_le_sum (fun i _ => abs_sub _ _)
    _ = (∑ i, |μ (A i)|) + ∑ i, |ν (A i)| := Finset.sum_add_distrib
    _ ≤ 2 := by linarith [μ.variation_fin A hA, ν.variation_fin A hA]

theorem UnitCharge.exists_close_localized {α : Type*} (μ ν : UnitCharge α) {n k : ℕ}
    (A : Fin k → Fin n → Set α) (B : Fin n → Set α) (C : Fin k → Set α) (F : Set α)
    (hC : Pairwise (fun i j => Disjoint (C i \ F) (C j \ F)))
    (ε : ℝ) (hsize : 8 * (n : ℝ) < (k : ℝ) * ε)
    (hB : ∀ i, |μ (B i) - ν (B i)| < ε / 6)
    (hAF : ∀ j i, |μ ((A j i ∩ C j) ∩ F) - ν ((A j i ∩ C j) ∩ F)| < ε / 6)
    (hBF : ∀ j i, |μ ((B i ∩ C j) ∩ F) - ν ((B i ∩ C j) ∩ F)| < ε / 6) :
    ∃ j, ∀ i, |μ ((A j i ∩ C j) ∪ (B i \ C j)) -
      ν ((A j i ∩ C j) ∪ (B i \ C j))| < ε := by
  classical
  by_contra h
  push_neg at h
  let v : Fin k → Fin n → ℝ := fun j i =>
    |μ ((A j i ∩ C j) \ F) - ν ((A j i ∩ C j) \ F)| +
      |μ ((B i ∩ C j) \ F) - ν ((B i ∩ C j) \ F)|
  have hv (j : Fin k) (i : Fin n) : 0 ≤ v j i := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hrow (j : Fin k) : ε / 2 ≤ ∑ i, v j i := by
    obtain ⟨i, hi⟩ := h j
    have hle := μ.split_difference_bound ν (A j i) (B i) (C j) F
    have hbig : ε / 2 ≤ v j i := by dsimp [v]; linarith [hB i, hAF j i, hBF j i]
    exact hbig.trans (Finset.single_le_sum (fun i _ => hv j i) (Finset.mem_univ i))
  have hcol (i : Fin n) : (∑ j, v j i) ≤ 4 := by
    have hd (U : Fin k → Set α) : Pairwise (fun j l =>
        Disjoint ((U j ∩ C j) \ F) ((U l ∩ C l) \ F)) := by
      intro j l hjl
      apply (hC hjl).mono
      · intro x hx
        exact ⟨hx.1.2, hx.2⟩
      · intro x hx
        exact ⟨hx.1.2, hx.2⟩
    have hA' := μ.sum_abs_diff_le_two ν (fun j => (A j i ∩ C j) \ F) (hd (fun j => A j i))
    have hB' := μ.sum_abs_diff_le_two ν (fun j => (B i ∩ C j) \ F) (hd (fun _ => B i))
    simp only [v, Finset.sum_add_distrib]
    linarith
  have hsumlow : (k : ℝ) * (ε / 2) ≤ ∑ j, ∑ i, v j i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hrow j)
  have hsumhigh : (∑ j, ∑ i, v j i) ≤ 4 * (n : ℝ) := by
    rw [Finset.sum_comm]
    simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcol i)
  linarith

end ThesisCommon
