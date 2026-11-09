import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Natural-order enumeration of the constant and dyadic Haar vectors.
The constant has index zero; position k of level n has index 2^n+k. -/

namespace ThesisCommon

abbrev LpHaarTreeIndex := Σ n : ℕ, Fin (2 ^ n)

def lpHaarEncode : Option LpHaarTreeIndex → ℕ
  | none => 0
  | some ⟨n, k⟩ => 2 ^ n + k.val

theorem lpHaar_pow_log2_le {i : ℕ} (hi : i ≠ 0) : 2 ^ i.log2 ≤ i := by
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 hi

theorem lpHaar_lt_pow_log2_succ (i : ℕ) : i < 2 ^ (i.log2 + 1) := by
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by decide) i

theorem lpHaar_log2_index (n : ℕ) (k : Fin (2 ^ n)) :
    (2 ^ n + k.val).log2 = n := by
  rw [Nat.log2_eq_log_two]
  apply Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _)
  rw [pow_succ]
  omega

theorem lpHaar_remainder_lt (i : ℕ) : i - 2 ^ i.log2 < 2 ^ i.log2 := by
  have h := lpHaar_lt_pow_log2_succ i
  have hp : 0 < 2 ^ i.log2 := pow_pos (by decide) _
  rw [pow_succ] at h
  omega

def lpHaarDecode (i : ℕ) : Option LpHaarTreeIndex :=
  if i = 0 then none else
    some ⟨i.log2, ⟨i - 2 ^ i.log2, lpHaar_remainder_lt i⟩⟩

@[simp] theorem lpHaarEncode_none : lpHaarEncode none = 0 := rfl

@[simp] theorem lpHaarEncode_some (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarEncode (some ⟨n, k⟩) = 2 ^ n + k.val := rfl

@[simp] theorem lpHaarDecode_zero : lpHaarDecode 0 = none := by simp [lpHaarDecode]

@[simp] theorem lpHaarDecode_index (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarDecode (2 ^ n + k.val) = some ⟨n, k⟩ := by
  have hne : 2 ^ n + k.val ≠ 0 := by have h : 0 < 2 ^ n := pow_pos (by decide) _; omega
  have hlog := lpHaar_log2_index n k
  simp only [lpHaarDecode, if_neg hne]
  apply congrArg some
  apply Sigma.ext hlog
  apply (Fin.heq_ext_iff (congrArg (fun m : ℕ => 2 ^ m) hlog)).mpr
  simp only [hlog, Nat.add_sub_cancel_left]

theorem lpHaarEncode_decode (i : ℕ) : lpHaarEncode (lpHaarDecode i) = i := by
  by_cases hi : i = 0
  · simp [hi]
  · simp only [lpHaarDecode, if_neg hi, lpHaarEncode]
    exact Nat.add_sub_of_le (lpHaar_pow_log2_le hi)

theorem lpHaarDecode_encode (i : Option LpHaarTreeIndex) :
    lpHaarDecode (lpHaarEncode i) = i := by
  rcases i with _ | ⟨n, k⟩
  · simp
  · exact lpHaarDecode_index n k

def lpHaarIndexEquiv : ℕ ≃ Option LpHaarTreeIndex where
  toFun := lpHaarDecode
  invFun := lpHaarEncode
  left_inv := lpHaarEncode_decode
  right_inv := lpHaarDecode_encode

theorem lpHaarEncode_injective : Function.Injective lpHaarEncode :=
  lpHaarIndexEquiv.symm.injective

end ThesisCommon
