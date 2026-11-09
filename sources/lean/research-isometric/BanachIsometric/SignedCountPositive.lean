import BanachIsometric.SignedFiberCount
import Mathlib.SetTheory.Cardinal.Finite

/-! # Actual finite positive-orientation fibers count their actual cardinality -/

namespace BanachIsometric

open Set
open scoped BigOperators

theorem signedFiberCount_eq_card_of_pos_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (D : E → E →L[ℝ] E) (s : Set E) (y : E)
    (hfin : {x : E | x ∈ s ∧ f x = y}.Finite)
    (hpos : ∀ x ∈ s, f x = y → 0 < (D x).det) :
    signedFiberCount f D s y = (Nat.card {x : E // x ∈ s ∧ f x = y} : ℤ) := by
  classical
  rw [signedFiberCount, dif_pos hfin]
  let F := {x : E // x ∈ s ∧ f x = y}
  letI : Fintype F := hfin.fintype
  change (∑ x : F, (SignType.sign (D x.val).det : ℤ)) = (Nat.card F : ℤ)
  have hsign (x : F) : (SignType.sign (D x.val).det : ℤ) = 1 := by
    rw [_root_.sign_eq_one_iff.mpr (hpos x.val x.property.1 x.property.2)]
    rfl
  simp only [hsign, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]

end BanachIsometric
