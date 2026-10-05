import Posets.OrdinalAmbientCoreBandsImage
import Posets.OrdinalClosedCoreCrossMassOperator
import Posets.WolfeClosedCover

/-! A single operator colour and genuine compact cores in infinitely many
disjoint ordinal blocks.  The cross-block variation is small at every point
of the selected cores, while their original ranks are unchanged. -/

noncomputable section
open Set Topology
universe u v
namespace Posets
open ThesisCommon

variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]

theorem ordinalAmbientCore_sequence_crossMass
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (θ γ : ℕ → Ordinal.{u}) (hθ : ∀ i, θ i ∈ ordinalTowerLevel (θ i) (γ i))
    (e : ∀ i, Iic (θ i) → K) (he : ∀ i, IsOpenEmbedding (e i))
    (hdisj : Pairwise (fun i j => Disjoint (range (e i)) (range (e j))))
    (a : ∀ i, ℕ → Iic (γ i)) (ha : ∀ i, Monotone (a i))
    {N : ℕ} {ε δ : ℝ} (hN : ‖T‖ + ‖S‖ < N * ε) (hδ : 0 < δ)
    (ρ : ℕ → Ordinal.{v}) (x : ∀ i, Iic (θ i))
    (hx : ∀ i, x i ∈ ordinalDerived (univ : Set (Iic (θ i))) (ρ i)) :
    ∃ (b : Bool) (k : ℕ → ℕ), StrictMono k ∧ ∃ (n : ℕ → Fin N) (C : ℕ → Set K),
      (∀ i, IsCompact (C i)) ∧
      (∀ i, C i ⊆ closure (e (k i) ''
        ordinalAmbientBandLeaves (hθ (k i)) (e (k i)) (he (k i)) M T S
          (a (k i)) (n i).val b ε)) ∧
      (∀ i, C i ⊆ range (e (k i))) ∧
      (∀ i, e (k i) (x (k i)) ∈ ordinalDerived (C i) (ρ (k i))) ∧
      ∀ i y, y ∈ C i → wolfeMass M (wolfeOperatorRow (if b then T else S) y)
        (wolfeCrossUnion (fun j => range (e (k j))) i) < δ := by
  classical
  have hex (i : ℕ) := ordinalAmbientCore_exists_coloured_image (hθ i) (e i) (he i)
    M T S hTS (a i) (ha i) hN (ρ i) (hx i)
  choose colour hc using hex
  obtain ⟨b, k₁, hk₁, hb⟩ := wolfe_finiteColor_subsequence (fun i => (colour i).2)
  let L : ℕ → Set K := fun i => e (k₁ i) ''
    ordinalAmbientBandLeaves (hθ (k₁ i)) (e (k₁ i)) (he (k₁ i)) M T S
      (a (k₁ i)) (colour (k₁ i)).1.val b ε
  let G : ℕ → Set K := fun i => range (e (k₁ i))
  have hGo (i : ℕ) : IsOpen (G i) := (he (k₁ i)).isOpen_range
  have hGc (i : ℕ) : IsCompact (G i) := by
    letI : CompactSpace (Iic (θ (k₁ i))) :=
      isCompact_iff_compactSpace.mp (ordinalClosedCore_interval_compact _)
    exact isCompact_range (he (k₁ i)).continuous
  have hGd : Pairwise (fun i j => Disjoint (G i) (G j)) := by
    intro i j hij
    exact hdisj (fun h => hij (hk₁.injective h))
  have hL (i : ℕ) : L i ⊆ G i := image_subset_range _ _
  have hr (i : ℕ) : e (k₁ i) (x (k₁ i)) ∈ ordinalDerived (closure (L i)) (ρ (k₁ i)) := by
    have hr' := (hc (k₁ i)).2.2
    simpa only [L, hb i] using hr'
  obtain ⟨k₂, hk₂, C, hCc, hCL, hCG, hCr, hCm⟩ := ordinalClosedCore_operator_crossMass M hK
    (if b then T else S) L G (fun i => e (k₁ i) (x (k₁ i))) (ρ ∘ k₁)
    hGo hGc hGd hL hr hδ
  exact ⟨b, k₁ ∘ k₂, hk₁.comp hk₂, fun i => (colour (k₁ (k₂ i))).1, C,
    hCc, hCL, hCG, hCr, hCm⟩

end Posets
