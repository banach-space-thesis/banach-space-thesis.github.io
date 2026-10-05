import Posets.CountableOrdinalPFPCofinalBands
import Posets.CountableOrdinalPFPBandRestriction
import Posets.WolfeRankedCrossMass

/-! One operator has disjoint cofinal norming bands with uniformly small
mass on every other chosen top cell. All ranks and local bounds survive. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}

theorem ordinalTower_exists_cofinal_cross_bands
    (hcθ : θ.card ≤ Cardinal.aleph0) (hcγ : γ.card ≤ Cardinal.aleph0)
    (hγ : IsSuccLimit γ) (hθ : θ ∈ ordinalTowerLevel θ γ)
    (hmul : ∀ β < γ, ∀ N : ℕ, β * N < γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _) {ε : ℝ} (hε : 0 < ε) :
    ∃ (b : Bool) (β : ℕ → Iio γ), StrictMono (fun n => (β n).val) ∧
      (∀ δ < γ, ∃ n, δ ≤ (β n).val) ∧
      ∃ (lower : ℕ → Iic γ)
        (F : ∀ n, OrdinalTowerNormingBand M (if b then T else S) (lower n) ε),
        (∀ n, (F n).top.level.val = (lower n).val + (β n).val) ∧
        Pairwise (fun n m => Disjoint (F n).top.cell (F m).top.cell) ∧
        ∀ n q, q ∈ (F n).base → wolfeMass M (wolfeOperatorRow (if b then T else S) q.point)
          (wolfeCrossUnion (fun m => (F m).top.cell) n) < ε := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (by
    have heq : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
    rw [← heq]
    exact isCompact_Icc)
  obtain ⟨b, β, hβ, hcof, lower, F, hgap, hd⟩ :=
    ordinalTower_exists_cofinal_norming_bands hcθ hcγ hγ hθ hmul M T S hTS hε
  let R := if b then T else S
  let v : OrdinalTowerNode θ γ → WolfeNode 𝕜 (Iic θ) :=
    OrdinalTowerNode.toWolfeNode (wolfeOperatorRow R)
  obtain ⟨k, hk, L, _, hrank, hcross⟩ := rankedWolfeFamily_exists_crossMass_subsequence M
    (JLMS.scattered_subtype JLMS.scattered_ordinal _) v (fun q => q.level.val)
    (fun n => (F n).base) (fun n => (F n).leaves) (fun n => (F n).top)
    (fun n => (F n).top.level.val) (fun n => (F n).top.cell)
    (fun n => (F n).top.cell_isClopen.2) hd (fun n => (F n).rank)
    (Q := ‖R‖) (fun _ q _ => wolfeOperatorRow_norm_le R q.point) hε
  let D (n : ℕ) := (F (k n)).restrictLeaves (L n) (hrank n)
  refine ⟨b, β ∘ k, hβ.comp hk, ?_, lower ∘ k, D, (fun n => hgap (k n)), ?_, ?_⟩
  · intro δ hδ
    obtain ⟨n, hn⟩ := hcof δ hδ
    exact ⟨n, hn.trans (hβ.monotone (hk.id_le n))⟩
  · intro n m hnm
    exact hd (fun h => hnm (hk.injective h))
  · intro n q hq
    exact hcross n q.level.val q hq

end Posets
