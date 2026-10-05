import ThesisCommon.Analysis.UnitCharge

/-! Finite-variation estimates for adjoining finitely many almost-disjoint sets. -/
noncomputable section
open Set
namespace ThesisCommon

theorem finite_disjoint_remainders {α ι : Type*} [Finite ι] (Z : ι → Set α)
    (hZ : Pairwise (fun i j => (Z i ∩ Z j).Finite)) :
    ∃ F : Set α, F.Finite ∧ Pairwise (fun i j => Disjoint (Z i \ F) (Z j \ F)) := by
  classical
  let F : Set α := ⋃ i, ⋃ j, if i = j then ∅ else Z i ∩ Z j
  have hF : F.Finite := Set.finite_iUnion (fun i => Set.finite_iUnion (fun j => by
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using hZ hij))
  refine ⟨F, hF, ?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  apply hxi.2
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, by simpa [hij] using And.intro hxi.1 hxj.1⟩⟩

theorem UnitCharge.split_difference_bound {α : Type*} (μ ν : UnitCharge α)
    (A B Z F : Set α) :
    |μ ((A ∩ Z) ∪ (B \ Z)) - ν ((A ∩ Z) ∪ (B \ Z))| ≤
      |μ B - ν B| + |μ ((A ∩ Z) \ F) - ν ((A ∩ Z) \ F)| +
      |μ ((B ∩ Z) \ F) - ν ((B ∩ Z) \ F)| +
      |μ ((A ∩ Z) ∩ F) - ν ((A ∩ Z) ∩ F)| +
      |μ ((B ∩ Z) ∩ F) - ν ((B ∩ Z) ∩ F)| := by
  have hμ := μ.split_test A B Z
  have hν := ν.split_test A B Z
  have hμA := μ.diff_add_inter (A ∩ Z) F
  have hνA := ν.diff_add_inter (A ∩ Z) F
  have hμB := μ.diff_add_inter (B ∩ Z) F
  have hνB := ν.diff_add_inter (B ∩ Z) F
  rw [abs_le]
  constructor <;> linarith [le_abs_self (μ B - ν B), neg_le_abs (μ B - ν B),
    le_abs_self (μ ((A ∩ Z) \ F) - ν ((A ∩ Z) \ F)),
    neg_le_abs (μ ((A ∩ Z) \ F) - ν ((A ∩ Z) \ F)),
    le_abs_self (μ ((B ∩ Z) \ F) - ν ((B ∩ Z) \ F)),
    neg_le_abs (μ ((B ∩ Z) \ F) - ν ((B ∩ Z) \ F)),
    le_abs_self (μ ((A ∩ Z) ∩ F) - ν ((A ∩ Z) ∩ F)),
    neg_le_abs (μ ((A ∩ Z) ∩ F) - ν ((A ∩ Z) ∩ F)),
    le_abs_self (μ ((B ∩ Z) ∩ F) - ν ((B ∩ Z) ∩ F)),
    neg_le_abs (μ ((B ∩ Z) ∩ F) - ν ((B ∩ Z) ∩ F))]

/-- If the old tests and finite overlaps are close, one of sufficiently many
disjoint remainders fails to separate. The stronger constant 8 implies the
paper's constant 12. -/
theorem UnitCharge.exists_close_split {α : Type*} (μ ν : UnitCharge α) {n k : ℕ}
    (A B : Fin n → Set α) (Z : Fin k → Set α) (F : Set α)
    (hZ : Pairwise (fun i j => Disjoint (Z i \ F) (Z j \ F)))
    (ε : ℝ) (hsize : 8 * (n : ℝ) < (k : ℝ) * ε)
    (hB : ∀ i, |μ (B i) - ν (B i)| < ε / 6)
    (hAF : ∀ j i, |μ ((A i ∩ Z j) ∩ F) - ν ((A i ∩ Z j) ∩ F)| < ε / 6)
    (hBF : ∀ j i, |μ ((B i ∩ Z j) ∩ F) - ν ((B i ∩ Z j) ∩ F)| < ε / 6) :
    ∃ j, ∀ i, |μ ((A i ∩ Z j) ∪ (B i \ Z j)) -
      ν ((A i ∩ Z j) ∪ (B i \ Z j))| < ε := by
  classical
  by_contra h
  push_neg at h
  let v : Fin k → Fin n → ℝ := fun j i =>
    |μ ((A i ∩ Z j) \ F) - ν ((A i ∩ Z j) \ F)| +
      |μ ((B i ∩ Z j) \ F) - ν ((B i ∩ Z j) \ F)|
  have hv (j : Fin k) (i : Fin n) : 0 ≤ v j i := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hrow (j : Fin k) : ε / 2 ≤ ∑ i, v j i := by
    obtain ⟨i, hi⟩ := h j
    have hle := μ.split_difference_bound ν (A i) (B i) (Z j) F
    have hbig : ε / 2 ≤ v j i := by dsimp [v]; linarith [hB i, hAF j i, hBF j i]
    exact hbig.trans (Finset.single_le_sum (fun i _ => hv j i) (Finset.mem_univ i))
  have hcol (i : Fin n) : (∑ j, v j i) ≤ 4 := by
    have hA' := μ.sum_abs_diff_inter_le_two ν (fun j => Z j \ F) hZ (A i)
    have hB' := μ.sum_abs_diff_inter_le_two ν (fun j => Z j \ F) hZ (B i)
    have hid (U V : Set α) : (U ∩ V) \ F = U ∩ (V \ F) := by ext x; simp; tauto
    simp only [v, Finset.sum_add_distrib, hid]
    linarith
  have hsumlow : (k : ℝ) * (ε / 2) ≤ ∑ j, ∑ i, v j i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hrow j)
  have hsumhigh : (∑ j, ∑ i, v j i) ≤ 4 * (n : ℝ) := by
    rw [Finset.sum_comm]
    simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcol i)
  linarith

end ThesisCommon
