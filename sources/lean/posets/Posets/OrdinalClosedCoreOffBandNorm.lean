import Posets.CZeroSupportedRestriction
import Posets.OrdinalClosedCoreCrossMassOperator

/-! Rank-preserving off-band operator selection. The small operator norm
is deduced from the actual atomic cross-mass pruning, not supplied as a
hypothesis. Every supported continuous function is controlled. The compact
cores and their Cantor--Bendixson ranks may be uncountable. -/
noncomputable section
namespace Posets
open Set Topology TopologicalSpace
open ThesisCommon
universe u
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem ordinalClosedCore_operator_offBandNorm
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (L G : ℕ → Set K) (root : ℕ → K) (γ : ℕ → Ordinal.{u})
    (hGopen : ∀ i, IsOpen (G i)) (hGcompact : ∀ i, IsCompact (G i))
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hL : ∀ i, L i ⊆ G i)
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ C : ℕ → Compacts K,
      (∀ i, (C i : Set K) ⊆ closure (L (k i))) ∧
      (∀ i, (C i : Set K) ⊆ G (k i)) ∧
      (∀ i, root (k i) ∈ ordinalDerived (C i : Set K) (γ (k i))) ∧
      (∀ i, ‖cZeroSupportedRead T (C i) (wolfeCrossUnion (G ∘ k) i)‖ ≤ ε) := by
  obtain ⟨k, hk, A, hcA, hAL, hAG, hr, hm⟩ :=
    ordinalClosedCore_operator_crossMass M hK T L G root γ hGopen hGcompact hG hL hroot hε
  refine ⟨k, hk, fun i => ⟨A i, hcA i⟩, hAL, hAG, hr, ?_⟩
  intro i
  exact norm_cZeroSupportedRead_le_of_mass M T ⟨A i, hcA i⟩
    (wolfeCrossUnion (G ∘ k) i) hε.le (fun x => (hm i x.val x.property).le)

end Posets
