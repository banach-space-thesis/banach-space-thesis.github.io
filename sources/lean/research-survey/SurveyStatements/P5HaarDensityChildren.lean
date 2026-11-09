import SurveyStatements.P5HaarDensityGrid

/-! Binary subdivision of the dyadic intervals. -/

noncomputable section
set_option autoImplicit false
open Set

namespace SurveyStatements.P5

def haarDensityLeftChild (I : DyadicIndex) : DyadicIndex :=
  ⟨I.1 + 1, ⟨2 * I.2.val, by
    have hi := I.2.isLt
    rw [pow_succ]
    omega⟩⟩

def haarDensityRightChild (I : DyadicIndex) : DyadicIndex :=
  ⟨I.1 + 1, ⟨2 * I.2.val + 1, by
    have hi := I.2.isLt
    rw [pow_succ]
    omega⟩⟩

theorem haarDensityLeftChild_endpoints (I : DyadicIndex) :
    dyadicStart (haarDensityLeftChild I) = dyadicStart I ∧
      dyadicEnd (haarDensityLeftChild I) = dyadicMiddle I := by
  have hN : (2 : ℝ) ^ I.1 ≠ 0 := by positivity
  constructor <;>
    simp only [dyadicStart, dyadicEnd, dyadicMiddle, haarDensityLeftChild,
      Nat.cast_mul, Nat.cast_ofNat, pow_succ] <;>
    field_simp <;> ring

theorem haarDensityRightChild_endpoints (I : DyadicIndex) :
    dyadicStart (haarDensityRightChild I) = dyadicMiddle I ∧
      dyadicEnd (haarDensityRightChild I) = dyadicEnd I := by
  have hN : (2 : ℝ) ^ I.1 ≠ 0 := by positivity
  constructor <;>
    simp only [dyadicStart, dyadicEnd, dyadicMiddle, haarDensityRightChild,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ] <;>
    field_simp <;> ring

theorem haarDensityLeftChild_cell (I : DyadicIndex) :
    haarDensityCell (haarDensityLeftChild I) = dyadicLeft I := by
  rw [haarDensityCell, (haarDensityLeftChild_endpoints I).1,
    (haarDensityLeftChild_endpoints I).2]
  rfl

theorem haarDensityRightChild_cell (I : DyadicIndex) :
    haarDensityCell (haarDensityRightChild I) = dyadicRight I := by
  rw [haarDensityCell, (haarDensityRightChild_endpoints I).1,
    (haarDensityRightChild_endpoints I).2]
  rfl

theorem haarDensityCell_union (I : DyadicIndex) :
    dyadicLeft I ∪ dyadicRight I = haarDensityCell I :=
  Ico_union_Ico_eq_Ico (dyadicEndpoints I).2.1 (dyadicEndpoints I).2.2.1

theorem haarDensityChildren_disjoint (I : DyadicIndex) :
    Disjoint (dyadicLeft I) (dyadicRight I) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact not_lt_of_ge hy.1 hx.2

theorem haarDensityCell_is_child (n : ℕ) (i : Fin (2 ^ (n + 1))) :
    ∃ j : Fin (2 ^ n),
      (⟨n + 1, i⟩ : DyadicIndex) = haarDensityLeftChild ⟨n, j⟩ ∨
        (⟨n + 1, i⟩ : DyadicIndex) = haarDensityRightChild ⟨n, j⟩ := by
  have hi : i.val < 2 ^ n * 2 := by simpa only [pow_succ] using i.isLt
  have hj : i.val / 2 < 2 ^ n := (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hi
  let j : Fin (2 ^ n) := ⟨i.val / 2, hj⟩
  refine ⟨j, ?_⟩
  have hm := Nat.mod_lt i.val (by norm_num : 0 < 2)
  by_cases heven : i.val % 2 = 0
  · left
    apply congrArg (fun z : Fin (2 ^ (n + 1)) => (⟨n + 1, z⟩ : DyadicIndex))
    apply Fin.ext
    change i.val = 2 * (i.val / 2)
    omega
  · right
    apply congrArg (fun z : Fin (2 ^ (n + 1)) => (⟨n + 1, z⟩ : DyadicIndex))
    apply Fin.ext
    change i.val = 2 * (i.val / 2) + 1
    omega

end SurveyStatements.P5
