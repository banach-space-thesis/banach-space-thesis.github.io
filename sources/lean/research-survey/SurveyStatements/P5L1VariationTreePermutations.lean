import SurveyStatements.P5L1VariationReynolds
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual finite dyadic tree group on terminal cells. Tree compatibility
is expressed by the quotient giving the ancestor prefix. XOR permutations
give transitivity at every depth, and the group is finite. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
namespace SurveyStatements.P5L1Variation

def samePrefix (M n : ℕ) (a b : Fin (2 ^ M)) : Prop :=
  a.val / 2 ^ (M - n) = b.val / 2 ^ (M - n)

def dyadicTreeGroup (M : ℕ) : Subgroup (Equiv.Perm (Fin (2 ^ M))) where
  carrier := {σ | ∀ n ≤ M, ∀ a b : Fin (2 ^ M),
    samePrefix M n a b ↔ samePrefix M n (σ a) (σ b)}
  one_mem' := by intro n hn a b; rfl
  mul_mem' := by
    intro σ τ hσ hτ n hn a b
    exact (hτ n hn a b).trans (hσ n hn (τ a) (τ b))
  inv_mem' := by
    intro σ hσ n hn a b
    simpa using (hσ n hn (σ⁻¹ a) (σ⁻¹ b)).symm

abbrev DyadicTreePerm (M : ℕ) := dyadicTreeGroup M

instance dyadicTreePermFintype (M : ℕ) : Fintype (DyadicTreePerm M) :=
  Fintype.ofFinite _

def dyadicTreeLeafAction (M : ℕ) :
    DyadicTreePerm M →* Equiv.Perm (Fin (2 ^ M)) := (dyadicTreeGroup M).subtype

theorem dyadicTreeLeafAction_prefix {M : ℕ} (σ : DyadicTreePerm M)
    (n : ℕ) (hn : n ≤ M) (a b : Fin (2 ^ M)) :
    samePrefix M n a b ↔ samePrefix M n (σ.val a) (σ.val b) :=
  σ.property n hn a b

def xorPermutation (M : ℕ) (mask : Fin (2 ^ M)) : Equiv.Perm (Fin (2 ^ M)) where
  toFun a := ⟨a.val ^^^ mask.val, Nat.xor_lt_two_pow a.isLt mask.isLt⟩
  invFun a := ⟨a.val ^^^ mask.val, Nat.xor_lt_two_pow a.isLt mask.isLt⟩
  left_inv a := by apply Fin.ext; simp [Nat.xor_assoc]
  right_inv a := by apply Fin.ext; simp [Nat.xor_assoc]

theorem xorPermutation_mem (M : ℕ) (mask : Fin (2 ^ M)) :
    xorPermutation M mask ∈ dyadicTreeGroup M := by
  intro n hn a b
  change a.val / 2 ^ (M - n) = b.val / 2 ^ (M - n) ↔
    (a.val ^^^ mask.val) / 2 ^ (M - n) = (b.val ^^^ mask.val) / 2 ^ (M - n)
  rw [Nat.xor_div_two_pow, Nat.xor_div_two_pow]
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg (fun x : ℕ => x ^^^ (mask.val / 2 ^ (M - n))) h
    simpa [Nat.xor_assoc] using h'

def xorTreePermutation (M : ℕ) (mask : Fin (2 ^ M)) : DyadicTreePerm M :=
  ⟨xorPermutation M mask, xorPermutation_mem M mask⟩

def prefixIndex (M n : ℕ) (hn : n ≤ M) (a : Fin (2 ^ M)) : Fin (2 ^ n) :=
  ⟨a.val / 2 ^ (M - n), by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (M - n))).mpr
    have hp : 2 ^ n * 2 ^ (M - n) = 2 ^ M := by
      rw [← pow_add, Nat.add_sub_of_le hn]
    simpa [hp] using a.isLt⟩

def prefixLift (M n : ℕ) (hn : n ≤ M) (a : Fin (2 ^ n)) : Fin (2 ^ M) :=
  ⟨a.val * 2 ^ (M - n), by
    have hp : 2 ^ n * 2 ^ (M - n) = 2 ^ M := by
      rw [← pow_add, Nat.add_sub_of_le hn]
    rw [← hp]
    exact Nat.mul_lt_mul_of_pos_right a.isLt (by positivity)⟩

@[simp] theorem prefixIndex_lift (M n : ℕ) (hn : n ≤ M) (a : Fin (2 ^ n)) :
    prefixIndex M n hn (prefixLift M n hn a) = a := by
  apply Fin.ext
  change (a.val * 2 ^ (M - n)) / 2 ^ (M - n) = a.val
  exact Nat.mul_div_cancel a.val (by positivity)

def nodeAction {M : ℕ} (σ : DyadicTreePerm M) (n : ℕ) (hn : n ≤ M)
    (a : Fin (2 ^ n)) : Fin (2 ^ n) :=
  prefixIndex M n hn (σ.val (prefixLift M n hn a))

theorem nodeAction_prefix {M : ℕ} (σ : DyadicTreePerm M) (n : ℕ) (hn : n ≤ M)
    (a : Fin (2 ^ M)) :
    prefixIndex M n hn (σ.val a) = nodeAction σ n hn (prefixIndex M n hn a) := by
  apply Fin.ext
  have h := (σ.property n hn a (prefixLift M n hn (prefixIndex M n hn a))).mp
    (by
      change a.val / 2 ^ (M - n) =
        (prefixLift M n hn (prefixIndex M n hn a)).val / 2 ^ (M - n)
      exact congrArg Fin.val (prefixIndex_lift M n hn (prefixIndex M n hn a)).symm)
  exact h

theorem nodeAction_injective {M : ℕ} (σ : DyadicTreePerm M) (n : ℕ) (hn : n ≤ M) :
    Function.Injective (nodeAction σ n hn) := by
  intro a b hab
  have h := (σ.property n hn (prefixLift M n hn a) (prefixLift M n hn b)).mpr
    (congrArg Fin.val hab)
  change (prefixIndex M n hn (prefixLift M n hn a)).val =
    (prefixIndex M n hn (prefixLift M n hn b)).val at h
  simpa using Fin.ext h

def nodePermutation {M : ℕ} (σ : DyadicTreePerm M) (n : ℕ) (hn : n ≤ M) :
    Equiv.Perm (Fin (2 ^ n)) :=
  Equiv.ofBijective (nodeAction σ n hn)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨nodeAction_injective σ n hn, rfl⟩)

theorem nodeAction_one (M n : ℕ) (hn : n ≤ M) (a : Fin (2 ^ n)) :
    nodeAction (1 : DyadicTreePerm M) n hn a = a :=
  prefixIndex_lift M n hn a

theorem nodeAction_mul {M : ℕ} (σ τ : DyadicTreePerm M)
    (n : ℕ) (hn : n ≤ M) (a : Fin (2 ^ n)) :
    nodeAction (σ * τ) n hn a = nodeAction σ n hn (nodeAction τ n hn a) := by
  change prefixIndex M n hn (σ.val (τ.val (prefixLift M n hn a))) = _
  exact nodeAction_prefix σ n hn (τ.val (prefixLift M n hn a))

def dyadicTreeNodeAction (M n : ℕ) (hn : n ≤ M) :
    DyadicTreePerm M →* Equiv.Perm (Fin (2 ^ n)) where
  toFun σ := nodePermutation σ n hn
  map_one' := by
    apply Equiv.ext
    intro a
    exact nodeAction_one M n hn a
  map_mul' σ τ := by
    apply Equiv.ext
    intro a
    exact nodeAction_mul σ τ n hn a

theorem dyadicTree_transitive (M n : ℕ) (hn : n ≤ M) (a b : Fin (2 ^ n)) :
    ∃ σ : DyadicTreePerm M, nodeAction σ n hn a = b := by
  let x := prefixLift M n hn a
  let y := prefixLift M n hn b
  let mask : Fin (2 ^ M) := ⟨x.val ^^^ y.val, Nat.xor_lt_two_pow x.isLt y.isLt⟩
  refine ⟨xorTreePermutation M mask, ?_⟩
  have hxy : (xorPermutation M mask) x = y := by
    apply Fin.ext
    change x.val ^^^ (x.val ^^^ y.val) = y.val
    rw [← Nat.xor_assoc]
    simp
  change prefixIndex M n hn ((xorPermutation M mask) x) = b
  rw [hxy]
  exact prefixIndex_lift M n hn b

end SurveyStatements.P5L1Variation

