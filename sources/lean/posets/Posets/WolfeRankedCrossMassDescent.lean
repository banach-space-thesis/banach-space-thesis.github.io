import Posets.WolfeRankedCrossMassStep

/-! Finite descent of the cross-mass budget. A negative leaf budget is
impossible because every retained root has a rank-zero descendant. -/
noncomputable section
open Set
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem rankedWolfeCrossMass_exists_of_budget (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u})
    (B L : ℕ → Set P) (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ rankedWolfeFamily v height (B i) (L i) (γ i))
    {Q ε : ℝ} (hε : 0 < ε)
    (hbudget : ∀ i q, q ∈ B i → height q = 0 → q ∈ L i →
      wolfeMass M (v q).1 (wolfeCrossUnion G i) ≤ Q) :
    RankedWolfeCrossMassSelection M v height B L root γ G ε := by
  classical
  by_contra hfail
  have hdesc (n : ℕ) : RankedWolfeCrossMassSelection M v height B L root γ G (Q - n * ε) := by
    induction n with
    | zero =>
        refine ⟨id, Function.injective_id, L, fun _ => Subset.rfl, hroot, ?_⟩
        simpa using hbudget
    | succ n ih =>
        obtain ⟨k, hk, L', hL', hr, hb⟩ := ih
        have hG' : Pairwise (fun i j => Disjoint ((G ∘ k) i) ((G ∘ k) j)) :=
          fun _ _ hij => hG (hk.ne hij)
        rcases rankedWolfeCrossMass_selection_or_decrease M v height (B ∘ k) L'
            (root ∘ k) (γ ∘ k) (G ∘ k) hG' hr hb with hs | hs
        · exact (hfail (RankedWolfeCrossMassSelection.comp M v height B L root γ G hk L' hL' hs)).elim
        · have h := RankedWolfeCrossMassSelection.comp M v height B L root γ G hk L' hL' hs
          convert h using 1
          push_cast
          ring
  obtain ⟨N, hN⟩ := exists_nat_gt (Q / ε)
  have hN' : Q < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  obtain ⟨k, _, L', _, hr, hb⟩ := hdesc N
  obtain ⟨q, hq, _⟩ := rankedWolfeFamily_exists_lower v height (B (k 0)) (L' 0)
    (γ (k 0)) (hr 0) (Ordinal.zero_le _)
  obtain ⟨hqB, hq0, hqL⟩ := (mem_rankedWolfeFamily_zero v height (B (k 0)) (L' 0) q).mp hq
  have hu := hb 0 q hqB hq0 hqL
  have hl := wolfeMass_nonneg M (v q).1 (wolfeCrossUnion (G ∘ k) 0)
  linarith

end Posets
