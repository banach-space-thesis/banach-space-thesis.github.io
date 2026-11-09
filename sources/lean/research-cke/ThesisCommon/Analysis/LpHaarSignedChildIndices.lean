import ThesisCommon.Analysis.LpHaarDyadicRefinement

/-! Both signed children of a finite Haar block are finite dyadic parents
at the next level. This gives the actual sets needed by the block recursion. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

def lpHaarSignedChildIndex (n : ℕ) (θ : Fin (2 ^ n) → Bool) :
    Fin (2 ^ n) ↪ Fin (2 ^ (n + 1)) where
  toFun k := ⟨2 * k.val + if θ k then 0 else 1, by
    have hk := k.isLt
    rw [pow_succ]
    cases θ k <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega⟩
  inj' := by
    intro k j h
    have hv : 2 * k.val + (if θ k then 0 else 1) =
        2 * j.val + (if θ j then 0 else 1) := congrArg Fin.val h
    have hk : (if θ k then 0 else 1 : ℕ) ≤ 1 := by split_ifs <;> omega
    have hj : (if θ j then 0 else 1 : ℕ) ≤ 1 := by split_ifs <;> omega
    apply Fin.ext
    omega

def lpHaarSignedChildAtoms (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) : Finset (Fin (2 ^ (n + 1))) :=
  S.map (lpHaarSignedChildIndex n θ)

theorem lpHaarSignedChildAtoms_parent (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    lpHaarBlockParent (n + 1) (lpHaarSignedChildAtoms n S θ) = lpHaarSignedPart n S θ := by
  ext x
  simp only [lpHaarBlockParent, lpHaarSignedPart, mem_iUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact ⟨k, hk, hx⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨lpHaarSignedChildIndex n θ k, Finset.mem_map.mpr ⟨k, hk, rfl⟩, hx⟩

theorem lpHaarSignedChildAtoms_nonempty (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (hS : S.Nonempty) (θ : Fin (2 ^ n) → Bool) : (lpHaarSignedChildAtoms n S θ).Nonempty :=
  hS.map

theorem lpHaarSignedChildAtoms_mass (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    ((lpHaarSignedChildAtoms n S θ).card : ℝ) * intervalLpDyadicRadius (n + 1) =
      ((S.card : ℝ) * intervalLpDyadicRadius n) / 2 := by
  simp only [lpHaarSignedChildAtoms, Finset.card_map, lpHaarRadius_succ]
  ring

end ThesisCommon
