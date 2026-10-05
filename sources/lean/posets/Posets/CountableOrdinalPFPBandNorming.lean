import Posets.CountableOrdinalPFPBandSelection
import Posets.WolfeLaminarSpan
import Posets.WolfeLaminarEmbeddingRankTop

/-! The surviving coordinates above the lower band endpoint have the full
offset quotient rank and a uniform lower bound on their indicator span. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}
variable {M : JLMS.AtomicDualModel 𝕜 (Iic θ)}
  {T : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ)}
  {lower : Iic γ} {ε : ℝ}

namespace OrdinalTowerNormingBand

def Coordinates (F : OrdinalTowerNormingBand M T lower ε) :=
  {q : OrdinalTowerNode θ γ // q ∈ F.base ∧ lower.val ≤ q.level.val}

theorem coordinate_countable (F : OrdinalTowerNormingBand M T lower ε) : Countable F.Coordinates := by
  exact (F.countable.mono (show {q : OrdinalTowerNode θ γ | q ∈ F.base ∧
    lower.val ≤ q.level.val} ⊆ F.base from fun _ h => h.1)).to_subtype

theorem finite_sum_lower_bound (hθ : θ ∈ ordinalTowerLevel θ γ)
    (F : OrdinalTowerNormingBand M T lower ε) (s : Finset F.Coordinates) (a : F.Coordinates → 𝕜) :
    ((1 / 2 : ℝ) - 4 * ε) *
      ‖∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) i.val.cell i.val.cell_isClopen i.val.cell_isCompact‖ ≤
      ‖T (∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) i.val.cell i.val.cell_isClopen i.val.cell_isCompact)‖ := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (by
    have heq : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
    rw [← heq]
    exact isCompact_Icc)
  letI : Nonempty (Iic θ) := ⟨⟨0, Ordinal.zero_le θ⟩⟩
  have heq : (1 / 2 : ℝ) - 4 * ε = (1 / 2 - ε) - 3 * ε := by ring
  rw [heq]
  apply wolfe_laminar_sum_lower_bound M T (fun i : F.Coordinates => i.val.cell)
    (fun i => rankedWolfeDescendantUnion (OrdinalTowerNode.toWolfeNode (wolfeOperatorRow T))
      F.base i.val) (fun i => wolfeOperatorRow T i.val.point)
    (fun i => i.val.cell_isClopen) (fun i => i.val.cell_isCompact) F.top.cell
    (fun i => F.cells i.val i.property.1) (fun i j => i.val.cell_laminar hθ j.val)
  · intro i j hji x hx
    exact ⟨j.val, j.property.1, hji, hx⟩
  · intro i
    exact wolfeOperatorRow_mem_adjointUnitBall T i.val.point
  · intro i
    exact (F.diagonal i.val i.property.1 i.property.2).trans (RCLike.re_le_norm _)
  · intro i
    exact F.outside i.val i.property.1 i.property.2
  · intro i
    exact (F.small i.val i.property.1).le

theorem quotient_rank (F : OrdinalTowerNormingBand M T lower ε)
    (α : Ordinal.{u}) (htop : F.top.level.val = lower.val + α) :
    (ThesisCommon.ordinalDerived (univ : Set (WolfeClopenTopQuotient F.top.cell
      (fun i : F.Coordinates => i.val.cell) (fun i => i.val.cell_isClopen))) α).Nonempty := by
  letI : CompactSpace F.top.cell := isCompact_iff_compactSpace.mp F.top.cell_isCompact
  apply (rankedWolfeFamily_clopenTop_ordinalDerived
    (OrdinalTowerNode.toWolfeNode (wolfeOperatorRow T)) (fun q => q.level.val)
    F.base F.leaves F.top.cell (fun i : F.Coordinates => i.val.cell)
    (fun i => i.val.cell_isClopen) lower.val ?_ ?_ α ?_ (Subset.rfl)).mono inter_subset_right
  · intro q _
    exact ⟨q.cell_nonempty, q.cell_isCompact⟩
  · intro δ q hq hδ _
    have hh := rankedWolfeFamily_base_height
      (OrdinalTowerNode.toWolfeNode (wolfeOperatorRow T)) (fun q => q.level.val)
      F.base F.leaves δ hq
    refine ⟨⟨q, hh.1, ?_⟩, rfl⟩
    change lower.val ≤ q.level.val
    simpa only [hh.2] using hδ
  · simpa only [htop] using F.rank

end OrdinalTowerNormingBand
end Posets
