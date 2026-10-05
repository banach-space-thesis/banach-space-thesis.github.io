import Posets.WolfeRankedCrossMassDescent
import Mathlib.Order.Filter.AtTopBot.Finite

/-! Wolfe's countable cross-block selection, with all original root ranks
preserved and strict small-mass bounds at every node of each pruned family. -/
noncomputable section
open Set Filter Topology
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]

local instance wolfeRankedCrossMassDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeRankedCrossMassDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

/-- The full countable cross-block selection: pass to an increasing
subsequence and restrict leaves without lowering any original root rank.
Every row in each resulting family has small mass on all other chosen roots. -/
theorem rankedWolfeFamily_exists_crossMass_subsequence (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (v : P → WolfeNode 𝕜 K)
    (height : P → Ordinal.{u}) (B L : ℕ → Set P) (root : ℕ → P)
    (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    (hGopen : ∀ i, IsOpen (G i)) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ rankedWolfeFamily v height (B i) (L i) (γ i))
    {Q : ℝ} (hnorm : ∀ i q, q ∈ B i → ‖WeakDual.toStrongDual (v q).1‖ ≤ Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ L' : ℕ → Set P,
      (∀ i, L' i ⊆ L (k i)) ∧
      (∀ i, root (k i) ∈ rankedWolfeFamily v height (B (k i)) (L' i) (γ (k i))) ∧
      ∀ i α q, q ∈ rankedWolfeFamily v height (B (k i)) (L' i) α →
        wolfeMass M (v q).1 (wolfeCrossUnion (G ∘ k) i) < ε := by
  classical
  obtain ⟨k, hk, L', hL', hr, hb⟩ := rankedWolfeCrossMass_exists_of_budget M v height B L root γ G
    hG hroot (half_pos hε)
    (fun i q hq _ _ => (wolfeMass_le_norm M (v q).1 _).trans (hnorm i q hq))
  obtain ⟨f, hf, hkf⟩ := Filter.strictMono_subseq_of_tendsto_atTop hk.nat_tendsto_atTop
  refine ⟨k ∘ f, hkf, L' ∘ f, fun i => hL' (f i), fun i => hr (f i), ?_⟩
  intro i α q hq
  have hle : wolfeMass M (v q).1 (wolfeCrossUnion (G ∘ (k ∘ f)) i) ≤ ε / 2 := by
    apply rankedWolfeFamily_mass_le_of_leaves M hK v height (B ((k ∘ f) i)) ((L' ∘ f) i)
      (wolfeCrossUnion_isOpen _ (fun j => hGopen _) i) ?_ α hq
    intro r hrB hr0 hrL
    exact (wolfeMass_mono M (v r).1 (wolfeCrossUnion_reindex_subset (G ∘ k) hf.injective i)).trans
      (hb (f i) r hrB hr0 hrL)
  exact hle.trans_lt (half_lt_self hε)

end Posets
