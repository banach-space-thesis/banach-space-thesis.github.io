import JLMS.OrderedFiniteRows
import Mathlib.Data.Fin.Tuple.Basic

/-! # Infinite disjoint coordinate families indexed by finite binary strings -/

noncomputable section
namespace JLMS

def binaryPrefix {n : ℕ} (a : Fin (n + 1) → Bool) : Fin n → Bool :=
  fun j => a j.castSucc

def binaryLast {n : ℕ} (a : Fin (n + 1) → Bool) : Bool := a (Fin.last n)

theorem binary_eq_of_prefix_last {n : ℕ} {a b : Fin (n + 1) → Bool}
    (hp : binaryPrefix a = binaryPrefix b) (hl : binaryLast a = binaryLast b) : a = b := by
  funext j
  refine Fin.lastCases hl (fun i => congrFun hp i) j

def splitBranchIndex {n : ℕ} (e : (Fin n → Bool) → ℕ → ℕ) (p : ℕ → ℕ)
    (a : Fin (n + 1) → Bool) (k : ℕ) : ℕ :=
  e (binaryPrefix a) (2 * p k + if binaryLast a then 1 else 0)

theorem splitBranchIndex_strictMono {n : ℕ}
    (e : (Fin n → Bool) → ℕ → ℕ) (p : ℕ → ℕ)
    (he : ∀ a, StrictMono (e a)) (hp : StrictMono p) (a : Fin (n + 1) → Bool) :
    StrictMono (splitBranchIndex e p a) := by
  intro k l hkl
  apply he (binaryPrefix a)
  have hh := hp hkl
  omega

theorem splitBranchIndex_injective {n : ℕ}
    (e : (Fin n → Bool) → ℕ → ℕ) (p : ℕ → ℕ)
    (he : Function.Injective (fun t : (Fin n → Bool) × ℕ => e t.1 t.2))
    (hp : Function.Injective p) :
    Function.Injective (fun t : (Fin (n + 1) → Bool) × ℕ => splitBranchIndex e p t.1 t.2) := by
  intro ⟨a, k⟩ ⟨b, l⟩ hab
  have hh := @he (binaryPrefix a, 2 * p k + if binaryLast a then 1 else 0)
    (binaryPrefix b, 2 * p l + if binaryLast b then 1 else 0) hab
  have hprefix : binaryPrefix a = binaryPrefix b := congrArg Prod.fst hh
  have hnum : 2 * p k + (if binaryLast a then 1 else 0) =
      2 * p l + (if binaryLast b then 1 else 0) := congrArg Prod.snd hh
  have hlast : binaryLast a = binaryLast b := by
    cases ha : binaryLast a <;> cases hb : binaryLast b <;>
      simp only [ha, hb, Bool.false_eq_true, if_false, if_true] at hnum ⊢ <;> omega
  have hpl : p k = p l := by
    rw [hlast] at hnum
    omega
  exact Prod.ext (binary_eq_of_prefix_last hprefix hlast) (hp hpl)

end JLMS
