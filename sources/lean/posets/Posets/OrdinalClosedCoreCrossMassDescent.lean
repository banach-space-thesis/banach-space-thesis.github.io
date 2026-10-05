import Posets.OrdinalClosedCoreCrossMassStep

/-! Finite descent terminates because nonempty closed-core rank forces
an actual selected leaf, which cannot have a negative variation mass. -/

noncomputable section
open Set
universe u
namespace Posets
open ThesisCommon
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace P] [T1Space P]

theorem ordinalClosedCoreCrossMass_exists_of_budget (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : ℕ → Set P)
    (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {Q ε : ℝ} (hε : 0 < ε)
    (hbudget : ∀ i q, q ∈ L i → wolfeMass M (v q) (wolfeCrossUnion G i) ≤ Q) :
    OrdinalClosedCoreCrossMassSelection M v L root γ G ε := by
  classical
  by_contra hfail
  have hdesc (n : ℕ) : OrdinalClosedCoreCrossMassSelection M v L root γ G (Q - n * ε) := by
    induction n with
    | zero =>
        refine ⟨id, Function.injective_id, L, fun _ => Subset.rfl, hroot, ?_⟩
        simpa using hbudget
    | succ n ih =>
        obtain ⟨k, hk, L', hL', hr, hb⟩ := ih
        have hG' : Pairwise (fun i j => Disjoint ((G ∘ k) i) ((G ∘ k) j)) :=
          fun _ _ hij => hG (hk.ne hij)
        rcases ordinalClosedCoreCrossMass_selection_or_decrease M v L'
            (root ∘ k) (γ ∘ k) (G ∘ k) hG' hr hb with hs | hs
        · exact (hfail (OrdinalClosedCoreCrossMassSelection.comp M v L root γ G hk L' hL' hs)).elim
        · have h := OrdinalClosedCoreCrossMassSelection.comp M v L root γ G hk L' hL' hs
          convert h using 1
          push_cast
          ring
  obtain ⟨N, hN⟩ := exists_nat_gt (Q / ε)
  have hN' : Q < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  obtain ⟨k, _, L', _, hr, hb⟩ := hdesc N
  have hp : root (k 0) ∈ closure (L' 0) := by
    simpa only [ordinalDerived_zero] using
      ordinalDerived_antitone isClosed_closure (Ordinal.zero_le (γ (k 0))) (hr 0)
  have hne : (L' 0).Nonempty := by
    by_contra h
    have he : L' 0 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp only [he, closure_empty, mem_empty_iff_false] at hp
  obtain ⟨q, hq⟩ := hne
  have hu := hb 0 q hq
  have hl := wolfeMass_nonneg M (v q) (wolfeCrossUnion (G ∘ k) 0)
  linarith

end Posets
