import Posets.IdealCounts

/-! The interval-upset count is invariant under an actual order isomorphism. -/
noncomputable section
namespace Posets

def intervalUpsetsEquivOfOrderIso {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) : IntervalUpsets P ≃ IntervalUpsets Q where
  toFun W := ⟨{i | (⟨(e.symm i.val.1, e.symm i.val.2), e.symm.monotone i.property⟩) ∈ W.val}, by
    intro i hi j hji hij
    exact W.property _ hi _ (e.symm.monotone hji) (e.symm.monotone hij)⟩
  invFun W := ⟨{i | (⟨(e i.val.1, e i.val.2), e.monotone i.property⟩) ∈ W.val}, by
    intro i hi j hji hij
    exact W.property _ hi _ (e.monotone hji) (e.monotone hij)⟩
  left_inv W := by
    apply Subtype.ext
    ext i
    simp
  right_inv W := by
    apply Subtype.ext
    ext i
    simp

theorem idealCount_orderIso {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [Finite P] [Finite Q] (e : P ≃o Q) : idealCount P = idealCount Q :=
  Nat.card_congr (intervalUpsetsEquivOfOrderIso e)

end Posets
