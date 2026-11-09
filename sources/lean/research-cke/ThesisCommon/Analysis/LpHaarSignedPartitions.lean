import ThesisCommon.Analysis.LpHaarDyadic

/-! The two children of a signed finite dyadic Haar block are actual
disjoint measurable sets of equal measure. They partition its parent.
These identities are the finite geometry of faithful Haar systems. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

def lpHaarSignedChild (n k : ℕ) (b : Bool) : Set ℝ :=
  lpHaarCell (n + 1) (2 * k + if b then 0 else 1)

theorem lpHaarSignedChild_measurable (n k : ℕ) (b : Bool) :
    MeasurableSet (lpHaarSignedChild n k b) := measurableSet_Ioc

theorem lpHaarSignedChild_union (n k : ℕ) (b : Bool) :
    lpHaarSignedChild n k b ∪ lpHaarSignedChild n k (!b) = lpHaarCell n k := by
  cases b <;> simp only [lpHaarSignedChild, Bool.false_eq_true, if_false, if_true,
    Bool.not_false, Bool.not_true, Nat.add_zero]
  · rw [union_comm]
    exact lpHaarCell_children n k
  · exact lpHaarCell_children n k

theorem lpHaarSignedChild_disjoint_other (n : ℕ) {k j : ℕ} (hkj : k ≠ j) (b c : Bool) :
    Disjoint (lpHaarSignedChild n k b) (lpHaarSignedChild n j c) := by
  apply lpHaarCell_disjoint_sameLevel
  cases b <;> cases c <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

theorem lpHaarSignedChild_disjoint_complement (n k : ℕ) (b : Bool) :
    Disjoint (lpHaarSignedChild n k b) (lpHaarSignedChild n k (!b)) := by
  apply lpHaarCell_disjoint_sameLevel
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true] <;> omega

theorem lpHaarSignedChild_measure (n k : ℕ) (hk : k < 2 ^ n) (b : Bool) :
    (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarSignedChild n k b) =
      ENNReal.ofReal (intervalLpDyadicRadius (n + 1)) := by
  apply lpHaarCell_measure
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> rw [pow_succ] <;> omega

def lpHaarSignedPart (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) : Set ℝ := ⋃ k ∈ S, lpHaarSignedChild n k (θ k)

def lpHaarBlockParent (n : ℕ) (S : Finset (Fin (2 ^ n))) : Set ℝ :=
  ⋃ k ∈ S, lpHaarCell n k

theorem lpHaarSignedPart_measurable (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) : MeasurableSet (lpHaarSignedPart n S θ) := by
  exact MeasurableSet.iUnion (fun k => MeasurableSet.iUnion
    (fun _ : k ∈ S => lpHaarSignedChild_measurable n k (θ k)))

theorem lpHaarSignedPart_union (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    lpHaarSignedPart n S θ ∪ lpHaarSignedPart n S (fun k => !(θ k)) = lpHaarBlockParent n S := by
  ext x
  simp only [lpHaarSignedPart, lpHaarBlockParent, mem_union, mem_iUnion]
  constructor
  · rintro (⟨k, hk, hx⟩ | ⟨k, hk, hx⟩)
    · exact ⟨k, hk, (lpHaarSignedChild_union n k (θ k)) ▸ Or.inl hx⟩
    · exact ⟨k, hk, (lpHaarSignedChild_union n k (θ k)) ▸ Or.inr hx⟩
  · rintro ⟨k, hk, hx⟩
    rw [← lpHaarSignedChild_union n k (θ k)] at hx
    rcases hx with hx | hx
    · exact Or.inl ⟨k, hk, hx⟩
    · exact Or.inr ⟨k, hk, hx⟩

theorem lpHaarSignedPart_disjoint (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    Disjoint (lpHaarSignedPart n S θ) (lpHaarSignedPart n S (fun k => !(θ k))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change x ∈ ⋃ k ∈ S, lpHaarSignedChild n k (θ k) at hx
  change x ∈ ⋃ k ∈ S, lpHaarSignedChild n k (!(θ k)) at hy
  simp only [mem_iUnion] at hx hy
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨j, hj, hxj⟩ := hy
  by_cases hij : i = j
  · subst j
    exact Set.disjoint_left.mp (lpHaarSignedChild_disjoint_complement n i (θ i)) hxi hxj
  · exact Set.disjoint_left.mp (lpHaarSignedChild_disjoint_other n
      (fun h => hij (Fin.ext h)) (θ i) (!(θ j))) hxi hxj

theorem lpHaarSignedPart_measure (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarSignedPart n S θ) =
      (S.card : ℝ≥0∞) * ENNReal.ofReal (intervalLpDyadicRadius (n + 1)) := by
  rw [lpHaarSignedPart, measure_biUnion_finset]
  · simp only [lpHaarSignedChild_measure n _ (Fin.isLt _) _, Finset.sum_const,
      nsmul_eq_mul]
  · intro i hi j hj hij
    exact lpHaarSignedChild_disjoint_other n (fun h => hij (Fin.ext h)) (θ i) (θ j)
  · intro k _
    exact lpHaarSignedChild_measurable n k (θ k)

theorem lpHaarSignedPart_equal_measure (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarSignedPart n S θ) =
      (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarSignedPart n S (fun k => !(θ k))) := by
  rw [lpHaarSignedPart_measure, lpHaarSignedPart_measure]

end ThesisCommon
