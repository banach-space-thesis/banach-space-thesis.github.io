import Posets.CountableOrdinalPFPBandNorming
import Posets.WolfeLaminarDisjointNorming

/-! Disjoint norming bands with small cross-mass give an actual isometric
c₀-sum insertion on which the chosen operator has a uniform lower bound. -/

noncomputable section
open Set Topology
universe u
namespace Posets
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}
variable {M : JLMS.AtomicDualModel 𝕜 (Iic θ)}
  {T : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ)}
  {lower : ℕ → Iic γ} {ε : ℝ}

abbrev OrdinalTowerNormingBand.Quotient {l : Iic γ}
    (F : OrdinalTowerNormingBand M T l ε) :=
  WolfeClopenTopQuotient F.top.cell (fun i : F.Coordinates => i.val.cell)
    (fun i => i.val.cell_isClopen)

variable (F : ∀ n, OrdinalTowerNormingBand M T (lower n) ε)

local instance countableOrdinalPFPBandSumTopCompact (n : ℕ) : CompactSpace (F n).top.cell :=
  isCompact_iff_compactSpace.mp (F n).top.cell_isCompact

def ordinalTowerBandsIsometry
    (hd : Pairwise (fun n m => Disjoint (F n).top.cell (F m).top.cell)) :
    JLMS.CZeroSum 𝕜 (fun n => C((F n).Quotient, 𝕜)) →ₗᵢ[𝕜] JLMS.CZero 𝕜 (Iic θ) :=
  wolfeLaminarDisjointSum (𝕜 := 𝕜) (fun n => (F n).top.cell)
    (fun n => (F n).top.cell_isClopen) hd
    (fun n (i : (F n).Coordinates) => i.val.cell) (fun _ i => i.val.cell_isClopen)

theorem ordinalTowerBands_finite_lower_bound (hθ : θ ∈ ordinalTowerLevel θ γ)
    (hd : Pairwise (fun n m => Disjoint (F n).top.cell (F m).top.cell)) (hε : 0 ≤ ε)
    (hcross : ∀ n q, q ∈ (F n).base → wolfeMass M (wolfeOperatorRow T q.point)
      (wolfeCrossUnion (fun m => (F m).top.cell) n) ≤ ε)
    (s : Finset (Σ n, (F n).Coordinates)) (a : (Σ n, (F n).Coordinates) → 𝕜) :
    ((1 / 2 : ℝ) - 7 * ε) * ‖∑ q ∈ s, a q • JLMS.clopenIndicator (𝕜 := 𝕜)
      q.2.val.cell q.2.val.cell_isClopen q.2.val.cell_isCompact‖ ≤
      ‖T (∑ q ∈ s, a q • JLMS.clopenIndicator (𝕜 := 𝕜)
        q.2.val.cell q.2.val.cell_isClopen q.2.val.cell_isCompact)‖ := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (by
    have heq : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
    rw [← heq]
    exact isCompact_Icc)
  letI : Nonempty (Iic θ) := ⟨⟨0, Ordinal.zero_le θ⟩⟩
  have heq : (1 / 2 : ℝ) - 7 * ε = (1 / 2 - ε) - 6 * ε := by ring
  rw [heq]
  apply wolfe_disjointBlocks_sum_lower_bound M T (fun n => (F n).top.cell) hd
    (fun n (i : (F n).Coordinates) => i.val.cell)
    (fun n i => rankedWolfeDescendantUnion (OrdinalTowerNode.toWolfeNode (wolfeOperatorRow T))
      (F n).base i.val) (fun _ i => wolfeOperatorRow T i.val.point)
    (fun _ i => i.val.cell_isClopen) (fun _ i => i.val.cell_isCompact)
    (fun n i => (F n).cells i.val i.property.1) (fun _ i => i.val.cell_nonempty)
    (fun _ i j => i.val.cell_laminar hθ j.val)
  · intro n i j hji x hx
    exact ⟨j.val, j.property.1, hji, hx⟩
  · intro _ i
    exact wolfeOperatorRow_mem_adjointUnitBall T i.val.point
  · exact hε
  · intro n i
    exact ((F n).diagonal i.val i.property.1 i.property.2).trans (RCLike.re_le_norm _)
  · intro n i
    exact (F n).outside i.val i.property.1 i.property.2
  · intro n i
    exact hcross n i.val i.property.1
  · intro n i
    exact ((F n).small i.val i.property.1).le

theorem ordinalTowerBands_lower_bound (hθ : θ ∈ ordinalTowerLevel θ γ)
    (hd : Pairwise (fun n m => Disjoint (F n).top.cell (F m).top.cell)) (hε : 0 ≤ ε)
    (hlower : ∀ n, (lower n).val ≤ (F n).top.level.val)
    (hcross : ∀ n q, q ∈ (F n).base → wolfeMass M (wolfeOperatorRow T q.point)
      (wolfeCrossUnion (fun m => (F m).top.cell) n) ≤ ε)
    (f : JLMS.CZeroSum 𝕜 (fun n => C((F n).Quotient, 𝕜))) :
    ((1 / 2 : ℝ) - 7 * ε) * ‖f‖ ≤ ‖T (ordinalTowerBandsIsometry F hd f)‖ := by
  apply wolfeLaminarDisjointSum_lower_bound (fun n => (F n).top.cell)
    (fun n => (F n).top.cell_isClopen) hd
    (fun n (i : (F n).Coordinates) => i.val.cell) (fun _ i => i.val.cell_isClopen)
    (fun _ i => i.val.cell_isCompact) (fun n i => (F n).cells i.val i.property.1)
    (fun n => ⟨⟨(F n).top, (F n).root_mem, hlower n⟩, rfl⟩)
    (fun _ i j => i.val.cell_laminar hθ j.val) T ((1 / 2 : ℝ) - 7 * ε)
    (ordinalTowerBands_finite_lower_bound F hθ hd hε hcross) f

end Posets
