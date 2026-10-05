import Posets.OrdinalClosedCoreOffBandNorm
import Posets.CZeroOffBandSynthesis

/-! Rank-preserving selection with a norm bound on the whole off-band
row of an actual disjoint c₀ synthesis. No finite-support restriction is
imposed on the input vectors. -/
noncomputable section
namespace Posets
open Set Topology TopologicalSpace
open ThesisCommon
universe u
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem ordinalClosedCore_operator_offBandSynthesis
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (L G : ℕ → Set K) (root : ℕ → K) (γ : ℕ → Ordinal.{u})
    (hGopen : ∀ i, IsOpen (G i)) (hGcompact : ∀ i, IsCompact (G i))
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hL : ∀ i, L i ⊆ G i)
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    (J : ∀ i, E i →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ → ℕ) (hk : StrictMono k), ∃ C : ℕ → Compacts K,
      (∀ i, (C i : Set K) ⊆ closure (L (k i))) ∧
      (∀ i, (C i : Set K) ⊆ G (k i)) ∧
      (∀ i, root (k i) ∈ ordinalDerived (C i : Set K) (γ (k i))) ∧
      (let hd : Pairwise (fun i j => Disjoint ((G ∘ k) i) ((G ∘ k) j)) :=
        fun i j hij => @hG (k i) (k j) (fun heq => hij (hk.injective heq))
       ∀ i, ‖(cZeroSupportedRead T (C i) (wolfeCrossUnion (G ∘ k) i)).comp
          (cZeroOffBandSynthesis (G ∘ k) hd (fun j => J (k j))
            (fun j f => hsupp (k j) f) i)‖ ≤ ε) := by
  obtain ⟨k, hk, C, hCL, hCG, hr, hn⟩ :=
    ordinalClosedCore_operator_offBandNorm M hK T L G root γ hGopen hGcompact hG hL hroot hε
  refine ⟨k, hk, C, hCL, hCG, hr, ?_⟩
  intro hd i
  exact norm_offBandCompression_le (G ∘ k) hd (fun j => J (k j))
    (fun j f => hsupp (k j) f) T (C i) i hε.le (hn i)

end Posets
