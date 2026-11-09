import ThesisCommon.Analysis.LpHaarSignedPartitions

/-! Refinement of an actual finite dyadic parent to any later level. The
set and its measure are preserved, so the interference selection lemma
can be applied with one fixed positive parent measure. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

def lpHaarParentIndex (n : ℕ) (j : Fin (2 ^ (n + 1))) : Fin (2 ^ n) :=
  ⟨j.val / 2, by
    have h : j.val < 2 ^ n * 2 := by simpa only [pow_succ] using j.isLt
    omega⟩

def lpHaarRefineOnce (n : ℕ) (S : Finset (Fin (2 ^ n))) : Finset (Fin (2 ^ (n + 1))) :=
  Finset.univ.filter (fun j => lpHaarParentIndex n j ∈ S)

theorem lpHaarBlockParent_refine_once (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    lpHaarBlockParent (n + 1) (lpHaarRefineOnce n S) = lpHaarBlockParent n S := by
  ext x
  simp only [lpHaarBlockParent, mem_iUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    have hmem : lpHaarParentIndex n j ∈ S := by simpa [lpHaarRefineOnce] using hj
    refine ⟨lpHaarParentIndex n j, hmem, ?_⟩
    rw [← lpHaarCell_children]
    have hdivision : j.val = 2 * (j.val / 2) ∨ j.val = 2 * (j.val / 2) + 1 := by omega
    rcases hdivision with he | he
    · apply Or.inl
      change x ∈ lpHaarCell (n + 1) (2 * (j.val / 2))
      rw [← he]
      exact hx
    · apply Or.inr
      change x ∈ lpHaarCell (n + 1) (2 * (j.val / 2) + 1)
      rw [← he]
      exact hx
  · rintro ⟨k, hk, hx⟩
    rw [← lpHaarCell_children] at hx
    have hbound : 2 * k.val + 1 < 2 ^ (n + 1) := by
      have h := k.isLt
      rw [pow_succ]
      omega
    rcases hx with hx | hx
    · let j : Fin (2 ^ (n + 1)) := ⟨2 * k.val, by omega⟩
      refine ⟨j, ?_, hx⟩
      have hj : lpHaarParentIndex n j = k := by apply Fin.ext; simp [lpHaarParentIndex, j]
      simp [lpHaarRefineOnce, hj, hk]
    · let j : Fin (2 ^ (n + 1)) := ⟨2 * k.val + 1, hbound⟩
      refine ⟨j, ?_, hx⟩
      have hj : lpHaarParentIndex n j = k := by
        apply Fin.ext
        change (2 * k.val + 1) / 2 = k.val
        omega
      simp [lpHaarRefineOnce, hj, hk]

def lpHaarRefine (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    (d : ℕ) → Finset (Fin (2 ^ (n + d)))
  | 0 => S
  | d + 1 => lpHaarRefineOnce (n + d) (lpHaarRefine n S d)

theorem lpHaarBlockParent_refine (n : ℕ) (S : Finset (Fin (2 ^ n))) (d : ℕ) :
    lpHaarBlockParent (n + d) (lpHaarRefine n S d) = lpHaarBlockParent n S := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change lpHaarBlockParent ((n + d) + 1)
      (lpHaarRefineOnce (n + d) (lpHaarRefine n S d)) = _
    rw [lpHaarBlockParent_refine_once, ih]

theorem lpHaarBlockParent_measure (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarBlockParent n S) =
      (S.card : ℝ≥0∞) * ENNReal.ofReal (intervalLpDyadicRadius n) := by
  rw [lpHaarBlockParent, measure_biUnion_finset]
  · simp only [lpHaarCell_measure n _ (Fin.isLt _), Finset.sum_const, nsmul_eq_mul]
  · intro i hi j hj hij
    exact lpHaarCell_disjoint_sameLevel n (fun h => hij (Fin.ext h))
  · intro k _
    exact measurableSet_Ioc

theorem lpHaarBlockParent_real_measure (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) =
      (S.card : ℝ) * intervalLpDyadicRadius n := by
  rw [measureReal_def, lpHaarBlockParent_measure, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]

theorem lpHaarRefine_mass (n : ℕ) (S : Finset (Fin (2 ^ n))) (d : ℕ) :
    ((lpHaarRefine n S d).card : ℝ) * intervalLpDyadicRadius (n + d) =
      (S.card : ℝ) * intervalLpDyadicRadius n := by
  rw [← lpHaarBlockParent_real_measure, lpHaarBlockParent_refine, lpHaarBlockParent_real_measure]

end ThesisCommon
