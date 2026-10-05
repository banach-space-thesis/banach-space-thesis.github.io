import ThesisCommon.Analysis.SigmaComplexUnitCharge

/-! The finite-variation estimate for arbitrary complex tests inside a chosen
almost-disjoint support. The same numerical constants as in the real argument
follow from the complex triangle inequality. -/
noncomputable section
open Set
namespace ThesisCommon

theorem ComplexUnitCharge.split_difference_bound {α : Type*} (μ ν : ComplexUnitCharge α)
    (A B Z F : Set α) :
    ‖μ ((A ∩ Z) ∪ (B \ Z)) - ν ((A ∩ Z) ∪ (B \ Z))‖ ≤
      ‖μ B - ν B‖ + ‖μ ((A ∩ Z) \ F) - ν ((A ∩ Z) \ F)‖ +
      ‖μ ((B ∩ Z) \ F) - ν ((B ∩ Z) \ F)‖ +
      ‖μ ((A ∩ Z) ∩ F) - ν ((A ∩ Z) ∩ F)‖ +
      ‖μ ((B ∩ Z) ∩ F) - ν ((B ∩ Z) ∩ F)‖ := by
  have heq : μ ((A ∩ Z) ∪ (B \ Z)) - ν ((A ∩ Z) ∪ (B \ Z)) =
      (μ B - ν B) + (μ ((A ∩ Z) \ F) - ν ((A ∩ Z) \ F)) -
      (μ ((B ∩ Z) \ F) - ν ((B ∩ Z) \ F)) +
      (μ ((A ∩ Z) ∩ F) - ν ((A ∩ Z) ∩ F)) -
      (μ ((B ∩ Z) ∩ F) - ν ((B ∩ Z) ∩ F)) := by
    rw [μ.split_test,ν.split_test,← μ.diff_add_inter (A ∩ Z) F,
      ← ν.diff_add_inter (A ∩ Z) F,← μ.diff_add_inter (B ∩ Z) F,← ν.diff_add_inter (B ∩ Z) F]
    ring
  rw [heq]
  calc
    _ ≤ ‖(μ B - ν B) + (μ ((A ∩ Z) \ F) - ν ((A ∩ Z) \ F)) -
        (μ ((B ∩ Z) \ F) - ν ((B ∩ Z) \ F)) +
        (μ ((A ∩ Z) ∩ F) - ν ((A ∩ Z) ∩ F))‖ +
        ‖μ ((B ∩ Z) ∩ F) - ν ((B ∩ Z) ∩ F)‖ := norm_sub_le _ _
    _ ≤ (‖(μ B - ν B) + (μ ((A ∩ Z) \ F) - ν ((A ∩ Z) \ F)) -
        (μ ((B ∩ Z) \ F) - ν ((B ∩ Z) \ F))‖ +
        ‖μ ((A ∩ Z) ∩ F) - ν ((A ∩ Z) ∩ F)‖) +
        ‖μ ((B ∩ Z) ∩ F) - ν ((B ∩ Z) ∩ F)‖ := add_le_add_right (norm_add_le _ _) _
    _ ≤ ((‖(μ B - ν B) + (μ ((A ∩ Z) \ F) - ν ((A ∩ Z) \ F))‖ +
        ‖μ ((B ∩ Z) \ F) - ν ((B ∩ Z) \ F)‖) +
        ‖μ ((A ∩ Z) ∩ F) - ν ((A ∩ Z) ∩ F)‖) +
        ‖μ ((B ∩ Z) ∩ F) - ν ((B ∩ Z) ∩ F)‖ :=
      add_le_add_right (add_le_add_right (norm_sub_le _ _) _) _
    _ ≤ _ := add_le_add_right (add_le_add_right (add_le_add_right (norm_add_le _ _) _) _) _

theorem ComplexUnitCharge.exists_close_localized {α : Type*} (μ ν : ComplexUnitCharge α) {n k : ℕ}
    (A : Fin k → Fin n → Set α) (B : Fin n → Set α) (C : Fin k → Set α) (F : Set α)
    (hC : Pairwise (fun i j => Disjoint (C i \ F) (C j \ F)))
    (ε : ℝ) (hsize : 8 * (n : ℝ) < (k : ℝ) * ε)
    (hB : ∀ i, ‖μ (B i) - ν (B i)‖ < ε / 6)
    (hAF : ∀ j i, ‖μ ((A j i ∩ C j) ∩ F) - ν ((A j i ∩ C j) ∩ F)‖ < ε / 6)
    (hBF : ∀ j i, ‖μ ((B i ∩ C j) ∩ F) - ν ((B i ∩ C j) ∩ F)‖ < ε / 6) :
    ∃ j, ∀ i, ‖μ ((A j i ∩ C j) ∪ (B i \ C j)) -
      ν ((A j i ∩ C j) ∪ (B i \ C j))‖ < ε := by
  classical
  by_contra h
  push_neg at h
  let v : Fin k → Fin n → ℝ := fun j i =>
    ‖μ ((A j i ∩ C j) \ F) - ν ((A j i ∩ C j) \ F)‖ +
      ‖μ ((B i ∩ C j) \ F) - ν ((B i ∩ C j) \ F)‖
  have hv (j : Fin k) (i : Fin n) : 0 ≤ v j i := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hrow (j : Fin k) : ε / 2 ≤ ∑ i, v j i := by
    obtain ⟨i,hi⟩ := h j
    have hle := μ.split_difference_bound ν (A j i) (B i) (C j) F
    have hbig : ε / 2 ≤ v j i := by dsimp [v]; linarith [hB i,hAF j i,hBF j i]
    exact hbig.trans (Finset.single_le_sum (fun i _ => hv j i) (Finset.mem_univ i))
  have hcol (i : Fin n) : (∑ j, v j i) ≤ 4 := by
    have hd (U : Fin k → Set α) : Pairwise (fun j l =>
        Disjoint ((U j ∩ C j) \ F) ((U l ∩ C l) \ F)) := by
      intro j l hjl
      apply (hC hjl).mono
      · intro x hx
        exact ⟨hx.1.2,hx.2⟩
      · intro x hx
        exact ⟨hx.1.2,hx.2⟩
    have hA' := μ.sum_norm_diff_le_two ν (fun j => (A j i ∩ C j) \ F) (hd (fun j => A j i))
    have hB' := μ.sum_norm_diff_le_two ν (fun j => (B i ∩ C j) \ F) (hd (fun _ => B i))
    simp only [v,Finset.sum_add_distrib]
    linarith
  have hsumlow : (k : ℝ) * (ε/2) ≤ ∑ j, ∑ i, v j i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hrow j)
  have hsumhigh : (∑ j, ∑ i, v j i) ≤ 4*(n : ℝ) := by
    rw [Finset.sum_comm]
    simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcol i)
  linarith

end ThesisCommon
