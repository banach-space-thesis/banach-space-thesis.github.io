import Posets.OrdinalClosedCoreCrossMassDescent
import Posets.WolfeOutsideMass
import Mathlib.Order.Filter.AtTopBot.Finite

/-! Cross-block pruning for actual closed Cantor--Bendixson cores.
The parameter spaces and ranks may be uncountable. Only the list of
disjoint output cells is countable. -/

noncomputable section
open Set Filter Topology
universe u
namespace Posets
open ThesisCommon
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace P] [T1Space P]

local instance ordinalClosedCoreCrossMassDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance ordinalClosedCoreCrossMassDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem ordinalClosedCore_exists_crossMass_leaves (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : ℕ → Set P)
    (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {Q : ℝ} (hnorm : ∀ i q, q ∈ L i → ‖WeakDual.toStrongDual (v q)‖ ≤ Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ L' : ℕ → Set P,
      (∀ i, L' i ⊆ L (k i)) ∧
      (∀ i, root (k i) ∈ ordinalDerived (closure (L' i)) (γ (k i))) ∧
      ∀ i q, q ∈ L' i → wolfeMass M (v q) (wolfeCrossUnion (G ∘ k) i) ≤ ε := by
  obtain ⟨k, hk, L', hL', hr, hb⟩ := ordinalClosedCoreCrossMass_exists_of_budget
    M v L root γ G hG hroot hε
    (fun i q hq => (wolfeMass_le_norm M (v q) _).trans (hnorm i q hq))
  obtain ⟨f, hf, hkf⟩ := Filter.strictMono_subseq_of_tendsto_atTop hk.nat_tendsto_atTop
  refine ⟨k ∘ f, hkf, L' ∘ f, fun i => hL' (f i), fun i => hr (f i), ?_⟩
  intro i q hq
  exact (wolfeMass_mono M (v q)
    (wolfeCrossUnion_reindex_subset (G ∘ k) hf.injective i)).trans (hb (f i) q hq)

variable [LocallyCompactSpace K] [T2Space K]

/-- With continuous rows and open cells, the bounds hold on the full closed
cores. In particular, their original ordinal ranks are retained. -/
theorem ordinalClosedCore_exists_crossMass_subsequence (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hv : Continuous v)
    (L : ℕ → Set P) (root : ℕ → P) (γ : ℕ → Ordinal.{u}) (G : ℕ → Set K)
    (hGopen : ∀ i, IsOpen (G i)) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {Q : ℝ} (hnorm : ∀ i q, q ∈ L i → ‖WeakDual.toStrongDual (v q)‖ ≤ Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ L' : ℕ → Set P,
      (∀ i, L' i ⊆ L (k i)) ∧
      (∀ i, root (k i) ∈ ordinalDerived (closure (L' i)) (γ (k i))) ∧
      ∀ i q, q ∈ closure (L' i) →
        wolfeMass M (v q) (wolfeCrossUnion (G ∘ k) i) < ε := by
  obtain ⟨k, hk, L', hL', hr, hb⟩ := ordinalClosedCore_exists_crossMass_leaves
    M v L root γ G hG hroot hnorm (half_pos hε)
  refine ⟨k, hk, L', hL', hr, ?_⟩
  intro i q hq
  have hclosed : IsClosed {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K) |
      wolfeMass M μ (wolfeCrossUnion (G ∘ k) i) ≤ ε / 2} := by
    simpa only [Set.compl_setOf, not_lt] using
      (isOpen_wolfeMass_gt M hK (wolfeCrossUnion_isOpen _ (fun j => hGopen _) i) (ε / 2)).isClosed_compl
  have hle : wolfeMass M (v q) (wolfeCrossUnion (G ∘ k) i) ≤ ε / 2 :=
    closure_minimal (fun x hx => hb i x hx) (hclosed.preimage hv) hq
  exact hle.trans_lt (half_lt_self hε)

end Posets
