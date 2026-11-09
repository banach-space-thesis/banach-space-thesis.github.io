import SurveyStatements.P5L1VariationTreePermutations

/-! Independent child flips in the genuine terminal dyadic tree. A flip is
the XOR of a lower bit inside one ancestor fiber and the identity outside.
The resulting actual leaf permutation is an involution in the finite group. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
namespace SurveyStatements.P5L1Variation

theorem prefix_div_comp (M n m a : ℕ) (hn : n ≤ M) (hm : m ≤ n) :
    (a / 2 ^ (M - n)) / 2 ^ (n - m) = a / 2 ^ (M - m) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  omega

theorem samePrefix_mono {M m n : ℕ} (hn : n ≤ M) (hm : m ≤ n)
    {a b : Fin (2 ^ M)} (h : samePrefix M n a b) : samePrefix M m a b := by
  change a.val / 2 ^ (M - m) = b.val / 2 ^ (M - m)
  rw [← prefix_div_comp M n m a.val hn hm, ← prefix_div_comp M n m b.val hn hm]
  exact congrArg (fun x : ℕ => x / 2 ^ (n - m)) h

def localXorLeaf (M n : ℕ) (k : Fin (2 ^ n)) (mask : Fin (2 ^ M))
    (a : Fin (2 ^ M)) : Fin (2 ^ M) :=
  if a.val / 2 ^ (M - n) = k.val then
    ⟨a.val ^^^ mask.val, Nat.xor_lt_two_pow a.isLt mask.isLt⟩ else a

theorem localXorLeaf_prefix (M n : ℕ) (k : Fin (2 ^ n)) (mask : Fin (2 ^ M))
    (hmask : mask.val < 2 ^ (M - n)) (a : Fin (2 ^ M)) :
    (localXorLeaf M n k mask a).val / 2 ^ (M - n) = a.val / 2 ^ (M - n) := by
  by_cases ha : a.val / 2 ^ (M - n) = k.val
  · simp only [localXorLeaf, if_pos ha]
    rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt hmask, Nat.xor_zero]
  · simp only [localXorLeaf, if_neg ha]

theorem localXorLeaf_involutive (M n : ℕ) (k : Fin (2 ^ n)) (mask : Fin (2 ^ M))
    (hmask : mask.val < 2 ^ (M - n)) :
    Function.Involutive (localXorLeaf M n k mask) := by
  intro a
  apply Fin.ext
  by_cases ha : a.val / 2 ^ (M - n) = k.val
  · have ha' : (localXorLeaf M n k mask a).val / 2 ^ (M - n) = k.val := by
      rw [localXorLeaf_prefix M n k mask hmask a, ha]
    rw [localXorLeaf, if_pos ha', localXorLeaf, if_pos ha]
    simp [Nat.xor_assoc]
  · have ha' : (localXorLeaf M n k mask a).val / 2 ^ (M - n) ≠ k.val := by
      rwa [localXorLeaf_prefix M n k mask hmask a]
    rw [localXorLeaf, if_neg ha', localXorLeaf, if_neg ha]

def localXorPermutation (M n : ℕ) (k : Fin (2 ^ n)) (mask : Fin (2 ^ M))
    (hmask : mask.val < 2 ^ (M - n)) : Equiv.Perm (Fin (2 ^ M)) where
  toFun := localXorLeaf M n k mask
  invFun := localXorLeaf M n k mask
  left_inv := localXorLeaf_involutive M n k mask hmask
  right_inv := localXorLeaf_involutive M n k mask hmask

theorem localXorPermutation_mem (M n : ℕ) (hn : n ≤ M)
    (k : Fin (2 ^ n)) (mask : Fin (2 ^ M)) (hmask : mask.val < 2 ^ (M - n)) :
    localXorPermutation M n k mask hmask ∈ dyadicTreeGroup M := by
  intro m hm a b
  change samePrefix M m a b ↔
    samePrefix M m (localXorLeaf M n k mask a) (localXorLeaf M n k mask b)
  by_cases hmn : m ≤ n
  · have hmask' : mask.val < 2 ^ (M - m) :=
      hmask.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hprefix (x : Fin (2 ^ M)) :
        (localXorLeaf M n k mask x).val / 2 ^ (M - m) = x.val / 2 ^ (M - m) := by
      by_cases hx : x.val / 2 ^ (M - n) = k.val
      · simp only [localXorLeaf, if_pos hx]
        rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt hmask', Nat.xor_zero]
      · simp only [localXorLeaf, if_neg hx]
    unfold samePrefix
    rw [hprefix a, hprefix b]
  · have hnm : n ≤ m := by omega
    by_cases ha : a.val / 2 ^ (M - n) = k.val
    · by_cases hb : b.val / 2 ^ (M - n) = k.val
      · unfold samePrefix
        simp only [localXorLeaf, if_pos ha, if_pos hb]
        rw [Nat.xor_div_two_pow, Nat.xor_div_two_pow]
        constructor
        · intro h
          rw [h]
        · intro h
          have h' := congrArg (fun x : ℕ => x ^^^ (mask.val / 2 ^ (M - m))) h
          simpa [Nat.xor_assoc] using h'
      · constructor
        · intro h
          have h' := samePrefix_mono hm hnm h
          exact False.elim (hb (h'.symm.trans ha))
        · intro h
          have h' := samePrefix_mono hm hnm h
          change (localXorLeaf M n k mask a).val / 2 ^ (M - n) =
            (localXorLeaf M n k mask b).val / 2 ^ (M - n) at h'
          rw [localXorLeaf_prefix M n k mask hmask a,
            localXorLeaf_prefix M n k mask hmask b] at h'
          exact False.elim (hb (h'.symm.trans ha))
    · by_cases hb : b.val / 2 ^ (M - n) = k.val
      · constructor
        · intro h
          have h' := samePrefix_mono hm hnm h
          exact False.elim (ha (h'.trans hb))
        · intro h
          have h' := samePrefix_mono hm hnm h
          change (localXorLeaf M n k mask a).val / 2 ^ (M - n) =
            (localXorLeaf M n k mask b).val / 2 ^ (M - n) at h'
          rw [localXorLeaf_prefix M n k mask hmask a,
            localXorLeaf_prefix M n k mask hmask b] at h'
          exact False.elim (ha (h'.trans hb))
      · unfold samePrefix
        simp only [localXorLeaf, if_neg ha, if_neg hb]

def localXorTreePermutation (M n : ℕ) (hn : n ≤ M)
    (k : Fin (2 ^ n)) (mask : Fin (2 ^ M)) (hmask : mask.val < 2 ^ (M - n)) :
    DyadicTreePerm M :=
  ⟨localXorPermutation M n k mask hmask,
    localXorPermutation_mem M n hn k mask hmask⟩

theorem localXorTreePermutation_involutive (M n : ℕ) (hn : n ≤ M)
    (k : Fin (2 ^ n)) (mask : Fin (2 ^ M)) (hmask : mask.val < 2 ^ (M - n)) :
    Function.Involutive (localXorTreePermutation M n hn k mask hmask).val :=
  localXorLeaf_involutive M n k mask hmask

end SurveyStatements.P5L1Variation

