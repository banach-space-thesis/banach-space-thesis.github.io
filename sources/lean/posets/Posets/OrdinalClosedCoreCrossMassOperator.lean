import Posets.OrdinalClosedCoreCrossMass
import Posets.CountableOrdinalPFPBands

/-! The closed-core cross-mass selection for actual operator rows on a
locally compact scattered space. Compact disjoint input cells supply
compact selected cores, with no countability assumption on their points. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]

theorem ordinalClosedCore_operator_crossMass (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (L G : ℕ → Set K) (root : ℕ → K) (γ : ℕ → Ordinal.{u})
    (hGopen : ∀ i, IsOpen (G i)) (hGcompact : ∀ i, IsCompact (G i))
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hL : ∀ i, L i ⊆ G i)
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ C : ℕ → Set K,
      (∀ i, IsCompact (C i)) ∧
      (∀ i, C i ⊆ closure (L (k i))) ∧
      (∀ i, C i ⊆ G (k i)) ∧
      (∀ i, root (k i) ∈ ordinalDerived (C i) (γ (k i))) ∧
      ∀ i x, x ∈ C i →
        wolfeMass M (wolfeOperatorRow T x) (wolfeCrossUnion (G ∘ k) i) < ε := by
  obtain ⟨k, hk, L', hL', hr, hm⟩ := ordinalClosedCore_exists_crossMass_subsequence
    M hK (wolfeOperatorRow T) (wolfeOperatorRow_continuous T) L root γ G hGopen hG hroot
    (Q := ‖T‖) (fun _ x _ => wolfeOperatorRow_norm_le T x) hε
  have hsub (i : ℕ) : closure (L' i) ⊆ G (k i) :=
    closure_minimal ((hL' i).trans (hL (k i))) (hGcompact (k i)).isClosed
  exact ⟨k, hk, fun i => closure (L' i),
    fun i => (hGcompact (k i)).of_isClosed_subset isClosed_closure (hsub i),
    fun i => closure_mono (hL' i), hsub, hr, hm⟩

end Posets
