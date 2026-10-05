import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-! The backward supporting-node induction of PFP Definition 3.5 and
Lemma 3.6. Terminal predicates live on genuine finite tuples of naturals;
each earlier level requires infinitely many supporting successors.
-/
noncomputable section
namespace ThesisCommon

/-- A predicate on terminal tuples has an infinitely supported root.
At depth zero there is one empty tuple; otherwise infinitely many first
coordinates must leave an infinitely supported remainder. -/
def InfinitelySupported : (n : ℕ) → ((Fin n → ℕ) → Prop) → Prop
  | 0, P => P Fin.elim0
  | n + 1, P => {i : ℕ | InfinitelySupported n (fun t => P (Fin.cons i t))}.Infinite

/-- Support of any fixed prefix, leaving r levels to be filled. This is
the source's nodewise definition; k=0 additionally permits the root. -/
def SupportsPrefix {k r : ℕ} (P : (Fin (k + r) → ℕ) → Prop)
    (node : Fin k → ℕ) : Prop :=
  InfinitelySupported r (fun tail => P (Fin.append node tail))

/-- If every terminal node has at least one of two colours, some colour
supports the root. This is the source's finite backward induction. -/
theorem infinitelySupported_or (n : ℕ) (P Q : (Fin n → ℕ) → Prop)
    (h : ∀ t, P t ∨ Q t) : InfinitelySupported n P ∨ InfinitelySupported n Q := by
  induction n with
  | zero => exact h Fin.elim0
  | succ n ih =>
    have hc (i : ℕ) :
        InfinitelySupported n (fun t => P (Fin.cons i t)) ∨
        InfinitelySupported n (fun t => Q (Fin.cons i t)) :=
      ih _ _ (fun t => h (Fin.cons i t))
    let A : Set ℕ := {i | InfinitelySupported n (fun t => P (Fin.cons i t))}
    by_cases hA : A.Infinite
    · exact Or.inl hA
    · apply Or.inr
      have hAc : Aᶜ.Infinite := (Set.not_infinite.mp hA).infinite_compl
      exact hAc.mono (fun i hi => (hc i).resolve_left hi)

/-- Monotonicity of support under enlargement of the terminal predicate. -/
theorem InfinitelySupported.mono {n : ℕ} {P Q : (Fin n → ℕ) → Prop}
    (h : InfinitelySupported n P) (hPQ : ∀ t, P t → Q t) : InfinitelySupported n Q := by
  induction n with
  | zero => exact hPQ Fin.elim0 h
  | succ n ih =>
    change {i : ℕ | InfinitelySupported n (fun t => P (Fin.cons i t))}.Infinite at h
    change {i : ℕ | InfinitelySupported n (fun t => Q (Fin.cons i t))}.Infinite
    exact Set.Infinite.mono (fun i hi => ih hi (fun t => hPQ (Fin.cons i t))) h

end ThesisCommon
