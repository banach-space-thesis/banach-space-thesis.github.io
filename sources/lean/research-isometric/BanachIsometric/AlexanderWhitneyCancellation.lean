import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Tactic

/-! The finite signed cancellation used by the actual Alexander--Whitney
chain identity. The two adjacent middle restrictions have opposite signs. -/

namespace BanachIsometric.SingularAW

open scoped BigOperators

theorem aw_signed_face_cancellation {M : Type*} [AddCommGroup M]
    (p q : ℕ) (a : Fin (p + 2) → M) (b : Fin (q + 2) → M)
    (v : Fin ((p + 1) + (q + 1)) → M)
    (hleft : ∀ i : Fin (p + 1), a i.castSucc = v (i.castAdd (q + 1)))
    (hright : ∀ j : Fin (q + 1), b j.succ = v (Fin.natAdd (p + 1) j))
    (hmiddle : a (Fin.last (p + 1)) = b 0) :
    (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • a i) +
        (-1 : ℤ) ^ p • (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • b j) =
      ∑ r : Fin ((p + 1) + (q + 1)), (-1 : ℤ) ^ r.val • v r := by
  conv_rhs => rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_castSucc (fun i : Fin (p + 2) => (-1 : ℤ) ^ i.val • a i),
    Fin.sum_univ_succ (fun j : Fin (q + 2) => (-1 : ℤ) ^ j.val • b j)]
  simp only [Fin.coe_castSucc, Fin.val_last, Fin.val_zero, pow_zero, one_smul,
    hleft, hright, hmiddle, Fin.coe_castAdd, Fin.coe_natAdd, Fin.val_succ,
    smul_add, Finset.smul_sum]
  have hsum : (∑ j : Fin (q + 1), (-1 : ℤ) ^ p •
        ((-1 : ℤ) ^ (j.val + 1) • v (Fin.natAdd (p + 1) j))) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • v (Fin.natAdd (p + 1) j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, ← pow_add]
    rw [show p + (j.val + 1) = p + 1 + j.val by omega]
  rw [hsum]
  have hmid : (-1 : ℤ) ^ (p + 1) • b 0 + (-1 : ℤ) ^ p • b 0 = 0 := by
    rw [← add_smul, pow_succ, mul_neg_one, neg_add_cancel, zero_smul]
  let L := ∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • v (i.castAdd (q + 1))
  let R := ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • v (Fin.natAdd (p + 1) j)
  change (L + (-1 : ℤ) ^ (p + 1) • b 0) + ((-1 : ℤ) ^ p • b 0 + R) = L + R
  calc
    _ = (L + R) + ((-1 : ℤ) ^ (p + 1) • b 0 + (-1 : ℤ) ^ p • b 0) := by abel
    _ = L + R := by rw [hmid, add_zero]

end BanachIsometric.SingularAW
