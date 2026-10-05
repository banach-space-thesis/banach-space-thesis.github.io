import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-! Finite-depth, infinitely splitting subtrees of ℕ^n. At each node an
injection chooses its infinitely many successors. The induced terminal map
is proved injective and preserves the recursive prefix structure by construction.
-/
noncomputable section
namespace ThesisCommon

/-- A tree embedding is an injection of first-level successors and a tree
embedding below each chosen successor. It carries no analytic conclusions. -/
def NatTreeEmbedding : ℕ → Type
  | 0 => PUnit
  | n + 1 => (ℕ ↪ ℕ) × (ℕ → NatTreeEmbedding n)

namespace NatTreeEmbedding

/-- The terminal-node map induced by the successive injections. -/
def map : {n : ℕ} → NatTreeEmbedding n → (Fin n → ℕ) → (Fin n → ℕ)
  | 0, _, t => t
  | _ + 1, f, t => Fin.cons (f.1 (t 0)) (map (f.2 (t 0)) (Fin.tail t))

theorem map_injective {n : ℕ} (f : NatTreeEmbedding n) : Function.Injective f.map := by
  induction n with
  | zero => intro x y _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro x y h
    have hhead : x 0 = y 0 := f.1.injective (by
      have hh := congrFun h 0
      simpa only [map, Fin.cons_zero] using hh)
    have htail : Fin.tail x = Fin.tail y := by
      have hh := congrArg Fin.tail h
      simp only [map, Fin.tail_cons, hhead] at hh
      exact ih (f.2 (y 0)) hh
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hhead, htail]

end NatTreeEmbedding
end ThesisCommon
