import Posets.WolfeRankedCrossMassLeaves

/-! One step of Wolfe's finite cross-mass budget descent. -/
noncomputable section
open Set
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

/-- An infinite selection preserving every original root rank and restricting
only its leaves, with a uniform cross-mass bound on rank-zero nodes. -/
def RankedWolfeCrossMassSelection (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u})
    (B L : ℕ → Set P) (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    (Q : ℝ) : Prop :=
  ∃ k : ℕ → ℕ, Function.Injective k ∧ ∃ L' : ℕ → Set P,
    (∀ i, L' i ⊆ L (k i)) ∧
    (∀ i, root (k i) ∈ rankedWolfeFamily v height (B (k i)) (L' i) (γ (k i))) ∧
    ∀ i q, q ∈ B (k i) → height q = 0 → q ∈ L' i →
      wolfeMass M (v q).1 (wolfeCrossUnion (G ∘ k) i) ≤ Q

theorem RankedWolfeCrossMassSelection.comp (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u})
    (B L : ℕ → Set P) (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    {k : ℕ → ℕ} (hk : Function.Injective k) (L' : ℕ → Set P)
    (hL : ∀ i, L' i ⊆ L (k i)) {Q : ℝ}
    (hs : RankedWolfeCrossMassSelection M v height (B ∘ k) L' (root ∘ k) (γ ∘ k) (G ∘ k) Q) :
    RankedWolfeCrossMassSelection M v height B L root γ G Q := by
  obtain ⟨j, hj, L'', hL'', hroot, hmass⟩ := hs
  exact ⟨k ∘ j, hk.comp hj, L'', fun i => (hL'' i).trans (hL (j i)), hroot, hmass⟩

/-- Partition the sequence into infinite rows. Either one row admits full-rank
small-mass pruning, or a diagonal sequence has a smaller mass budget. -/
theorem rankedWolfeCrossMass_selection_or_decrease (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u})
    (B L : ℕ → Set P) (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ rankedWolfeFamily v height (B i) (L i) (γ i))
    {Q ε : ℝ}
    (hbudget : ∀ i q, q ∈ B i → height q = 0 → q ∈ L i →
      wolfeMass M (v q).1 (wolfeCrossUnion G i) ≤ Q) :
    RankedWolfeCrossMassSelection M v height B L root γ G ε ∨
      RankedWolfeCrossMassSelection M v height B L root γ G (Q - ε) := by
  classical
  let S (r j : ℕ) : Set P := {q |
    wolfeMass M (v q).1 (wolfeCrossUnion (fun n => G (Nat.pair r n)) j) ≤ ε}
  by_cases hgood : ∃ r, ∀ j, root (Nat.pair r j) ∈
      rankedWolfeFamily v height (B (Nat.pair r j)) (L (Nat.pair r j) ∩ S r j) (γ (Nat.pair r j))
  · obtain ⟨r, hr⟩ := hgood
    left
    exact ⟨Nat.pair r, wolfePairRow_injective r, fun j => L (Nat.pair r j) ∩ S r j,
      fun _ => inter_subset_left, hr, fun _ _ _ _ hq => hq.2⟩
  · push_neg at hgood
    choose s hs using hgood
    let L' (r : ℕ) : Set P := L (Nat.pair r (s r)) \ S r (s r)
    have hroot' (r : ℕ) : root (Nat.pair r (s r)) ∈
        rankedWolfeFamily v height (B (Nat.pair r (s r))) (L' r) (γ (Nat.pair r (s r))) :=
      (rankedWolfeFamily_inter_or_diff v height (B (Nat.pair r (s r)))
        (L (Nat.pair r (s r))) (S r (s r)) _ (hroot (Nat.pair r (s r)))).resolve_left (hs r)
    right
    refine ⟨fun r => Nat.pair r (s r), wolfePairDiagonal_injective s, L',
      fun _ => diff_subset, hroot', ?_⟩
    intro r q hB hh hL
    apply wolfeCrossUnion_pair_budget M G hG s r (v q).1
      (hbudget _ q hB hh hL.1)
    exact le_of_lt (lt_of_not_ge hL.2)

end Posets
