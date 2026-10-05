import Posets.WolfeRankedCrossMassSets
import ThesisCommon.Analysis.OrdinalDerived

/-! A closed-core version of the finite cross-mass budget descent.
The retained rank is actual Cantor--Bendixson rank of the closure of the
selected leaves. No sequential representation of that rank is required. -/

noncomputable section
open Set
universe u
namespace Posets
open ThesisCommon
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace P] [T1Space P]

theorem ordinalDerived_closure_inter_or_diff (L S : Set P) (α : Ordinal.{u})
    {p : P} (hp : p ∈ ordinalDerived (closure L) α) :
    p ∈ ordinalDerived (closure (L ∩ S)) α ∨
      p ∈ ordinalDerived (closure (L \ S)) α := by
  classical
  have hL : L = (L ∩ S) ∪ (L \ S) := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_diff]
    tauto
  rw [hL, closure_union, ordinalDerived_union isClosed_closure isClosed_closure] at hp
  exact hp

/-- An injective subsequence with preserved closed-core ranks and a common
cross-mass bound on its selected leaves. -/
def OrdinalClosedCoreCrossMassSelection (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : ℕ → Set P)
    (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K) (Q : ℝ) : Prop :=
  ∃ k : ℕ → ℕ, Function.Injective k ∧ ∃ L' : ℕ → Set P,
    (∀ i, L' i ⊆ L (k i)) ∧
    (∀ i, root (k i) ∈ ordinalDerived (closure (L' i)) (γ (k i))) ∧
    ∀ i q, q ∈ L' i → wolfeMass M (v q) (wolfeCrossUnion (G ∘ k) i) ≤ Q

omit [T1Space P] in
theorem OrdinalClosedCoreCrossMassSelection.comp (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : ℕ → Set P)
    (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    {k : ℕ → ℕ} (hk : Function.Injective k) (L' : ℕ → Set P)
    (hL : ∀ i, L' i ⊆ L (k i)) {Q : ℝ}
    (hs : OrdinalClosedCoreCrossMassSelection M v L' (root ∘ k) (γ ∘ k) (G ∘ k) Q) :
    OrdinalClosedCoreCrossMassSelection M v L root γ G Q := by
  obtain ⟨j, hj, L'', hL'', hroot, hmass⟩ := hs
  exact ⟨k ∘ j, hk.comp hj, L'', fun i => (hL'' i).trans (hL (j i)), hroot, hmass⟩

/-- Either an infinite row already has small cross mass, or choosing one
bad coordinate in each row decreases the remaining mass budget by ε. -/
theorem ordinalClosedCoreCrossMass_selection_or_decrease (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : ℕ → Set P)
    (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {Q ε : ℝ}
    (hbudget : ∀ i q, q ∈ L i → wolfeMass M (v q) (wolfeCrossUnion G i) ≤ Q) :
    OrdinalClosedCoreCrossMassSelection M v L root γ G ε ∨
      OrdinalClosedCoreCrossMassSelection M v L root γ G (Q - ε) := by
  classical
  let S (r j : ℕ) : Set P := {q |
    wolfeMass M (v q) (wolfeCrossUnion (fun n => G (Nat.pair r n)) j) ≤ ε}
  by_cases hgood : ∃ r, ∀ j, root (Nat.pair r j) ∈
      ordinalDerived (closure (L (Nat.pair r j) ∩ S r j)) (γ (Nat.pair r j))
  · obtain ⟨r, hr⟩ := hgood
    left
    exact ⟨Nat.pair r, wolfePairRow_injective r, fun j => L (Nat.pair r j) ∩ S r j,
      fun _ => inter_subset_left, hr, fun _ _ hq => hq.2⟩
  · push_neg at hgood
    choose s hs using hgood
    let L' (r : ℕ) : Set P := L (Nat.pair r (s r)) \ S r (s r)
    have hroot' (r : ℕ) : root (Nat.pair r (s r)) ∈
        ordinalDerived (closure (L' r)) (γ (Nat.pair r (s r))) :=
      (ordinalDerived_closure_inter_or_diff (L (Nat.pair r (s r))) (S r (s r))
        (γ (Nat.pair r (s r))) (hroot (Nat.pair r (s r)))).resolve_left (hs r)
    right
    refine ⟨fun r => Nat.pair r (s r), wolfePairDiagonal_injective s, L',
      fun _ => diff_subset, hroot', ?_⟩
    intro r q hL
    apply wolfeCrossUnion_pair_budget M G hG s r (v q) (hbudget _ q hL.1)
    exact le_of_lt (lt_of_not_ge hL.2)

end Posets
