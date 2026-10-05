import Posets.OrdinalColouredBandLocalInverse
import Posets.CZeroCenteredInverseAssembly

/-! Actual coloured ordinal cores supply all the local inverses in the
global c₀ factorization. The retained geometric and cross-mass hypotheses
are explicit; local factorization is a conclusion, never an assumption. -/
noncomputable section
namespace Posets
open Set Filter Topology
open ThesisCommon
universe u v
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2400000

theorem ordinalColouredCofinal_factorization
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (θ γ upper lower b : ℕ → Ordinal.{u}) (F : ℕ → Set Ordinal.{u})
    (hθ : ∀ i, θ i ∈ ordinalTowerLevel (θ i) (γ i))
    (e : ∀ i, Iic (θ i) → K) (he : ∀ i, IsOpenEmbedding (e i))
    (hdisj : Pairwise (fun i j => Disjoint (range (e i)) (range (e j))))
    (a : ∀ i, ℕ → Iic (γ i)) (ha : ∀ i, Monotone (a i)) (n : ℕ → ℕ) (c : Bool)
    {ε δ η : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hgap : δ + η < 1 / 2 - 3 * ε)
    (G : ∀ i, OrdinalSeparatedBandCoreGeometry (F i) (θ i) (upper i) (lower i) (b i))
    (hlower : ∀ i, (a i (n i)).val = lower i)
    (hupper : ∀ i, (a i (n i+1)).val = upper i)
    (hF : ∀ i, F i ⊆ Subtype.val '' closure
      (ordinalAmbientBandLeaves (hθ i) (e i) (he i) M T S (a i) (n i) c ε))
    (z : K)
    (hconv : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, range (e i) ⊆ U)
    (hcross : ∀ i y, y ∈ e i '' ((Subtype.val : Iic (θ i) → Ordinal.{u}) ⁻¹' F i) →
      wolfeMass M (wolfeOperatorRow (if c then T else S) y)
        (wolfeCrossUnion (fun j => range (e j)) i) ≤ δ)
    (hz : ∀ g : JLMS.CZero 𝕜 K, Function.support g ⊆ ⋃ i, range (e i) →
      ‖(if c then T else S) g z‖ ≤ η * ‖g‖) :
    ∃ J : JLMS.CZeroSum 𝕜 (fun i => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b i)) →ₗᵢ[𝕜]
        JLMS.CZero 𝕜 K,
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜]
        JLMS.CZeroSum 𝕜 (fun i => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b i)),
      R.comp ((if c then T else S).comp J.toContinuousLinearMap) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 2 / ((1 / 2 - 3 * ε) - (δ + η)) := by
  classical
  have hpos : 0 < 1 / 2 - 3 * ε := (add_nonneg hδ hη).trans_lt hgap
  have hg : 3 * ε < 1 / 2 := sub_pos.mp hpos
  choose J q B hB hn hs hq using fun i =>
    ordinalSeparatedBand_coordinate_inverse_of_colour (hθ i) (e i) (he i) M T S
      (a i) (ha i) (n i) c hε hg (G i) (hlower i) (hupper i) (hF i)
  have hqconv : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U := by
    intro U hU
    filter_upwards [hconv U hU] with i hi
    intro x
    exact hi (image_subset_range _ _ (hq i x))
  obtain ⟨R, hR, hRn⟩ := exists_centered_cZero_factor_of_coordinate_inverses
    (fun i => range (e i)) hdisj J hs M (if c then T else S) q z hqconv B
    hpos hδ hη hgap hn hB (fun i x => hcross i (q i x) (hq i x)) hz
  exact ⟨wolfeDisjointSumIsometry (fun i => range (e i)) hdisj J hs, R, hR, hRn⟩

end Posets
