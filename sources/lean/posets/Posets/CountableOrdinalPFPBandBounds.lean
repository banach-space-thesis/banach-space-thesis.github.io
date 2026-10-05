import Posets.CountableOrdinalPFPBandColours
import Posets.WolfeRankedBounds
import JLMS.OrdinalScattered

/-! The single selected leaf colour controls all intermediate ranks in its
ancestor band. Fixed clopen indicator evaluations and open-set mass bounds
pass to every ancestor through the genuine weak-star closure theorem. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}

theorem ordinalTowerBandColour_leaf_estimates (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (a : ℕ → Iic γ) (n : ℕ) (b : Bool) (ε : ℝ)
    (top q r : OrdinalTowerNode θ γ) (htop : top.level = a (n+1))
    (hqtop : q.cell ⊆ top.cell) (hlow : (a n).val ≤ q.level.val)
    (hrq : r.cell ⊆ q.cell) (hr : r ∈ ordinalTowerBandColour hθ M T S a n b ε) :
    ∃ hp : r.level.val ≤ (a n).val,
      r.bandCell (a n) ⊆ q.cell ∧
      (1 / 2 : ℝ) ≤ RCLike.re (wolfeOperatorRow (if b then T else S) r.point
        (JLMS.clopenIndicator (r.bandCell (a n)) (r.bandCell_isClopen hθ (a n) hp)
          (r.bandCell_isCompact hθ (a n) hp))) ∧
      wolfeMass M (wolfeOperatorRow (if b then T else S) r.point)
        (top.cell \ r.bandCell (a n)) ≤ ε := by
  obtain ⟨hT, hS, hp, hdiag⟩ := hr
  have hrpoint : r.point ∈ q.cell := hrq r.point_mem_cell
  have heq : r.bandCell (a (n+1)) = top.cell := by
    rw [← htop]
    exact r.bandCell_eq_of_point_mem top (hqtop hrpoint)
  refine ⟨hp, r.bandCell_subset_of_point_mem hθ q (a n) hlow hrpoint, hdiag, ?_⟩
  rw [← heq]
  cases b with
  | false => exact hS.le
  | true => exact hT.le

theorem ordinalTower_coloured_band_bounds (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (a : ℕ → Iic γ) (n : ℕ) (b : Bool) (ε : ℝ)
    (top q : OrdinalTowerNode θ γ) (htop : top.level = a (n+1))
    (hqtop : q.cell ⊆ top.cell) (hlow : (a n).val ≤ q.level.val)
    (hq : q ∈ rankedWolfeFamily (OrdinalTowerNode.toWolfeNode (wolfeDirac (𝕜 := 𝕜)))
      (fun p => p.level.val) univ (ordinalTowerBandColour hθ M T S a n b ε) q.level.val) :
    wolfeMass M (wolfeOperatorRow (if b then T else S) q.point) (top.cell \ q.cell) ≤ ε ∧
      (1 / 2 : ℝ) - ε ≤ RCLike.re (wolfeOperatorRow (if b then T else S) q.point
        (JLMS.clopenIndicator q.cell q.cell_isClopen q.cell_isCompact)) := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (by
    have heq : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
    rw [← heq]
    exact isCompact_Icc)
  let R := if b then T else S
  let v : OrdinalTowerNode θ γ → WolfeNode 𝕜 (Iic θ) :=
    OrdinalTowerNode.toWolfeNode (wolfeOperatorRow R)
  let L := ordinalTowerBandColour hθ M T S a n b ε
  have hqR : q ∈ rankedWolfeFamily v (fun p => p.level.val) univ L q.level.val :=
    rankedWolfeFamily_operator_rows (fun p : OrdinalTowerNode θ γ => p.point)
      (fun p => p.cell) (fun p => p.level.val) univ L R q.level.val hq
  have hleaf (r : OrdinalTowerNode θ γ)
      (hr : r ∈ rankedWolfeFamily v (fun p => p.level.val) univ L 0)
      (hrq : r.cell ⊆ q.cell) :=
    ordinalTowerBandColour_leaf_estimates hθ M T S a n b ε top q r htop hqtop hlow hrq
      ((mem_rankedWolfeFamily_zero v (fun p => p.level.val) univ L r).mp hr).2.2
  constructor
  · apply rankedWolfeFamily_outside_le M (JLMS.scattered_subtype JLMS.scattered_ordinal _)
      v (fun p => p.level.val) univ L q.level.val hqR top.cell_isClopen.2 q.cell_isClopen.1
    intro r hr hrq
    obtain ⟨_, hU, _, hmass⟩ := hleaf r hr hrq
    exact (wolfeMass_mono M (wolfeOperatorRow R r.point) (diff_subset_diff_right hU)).trans hmass
  · have hclosed : IsClosed {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 (Iic θ)) |
        (1 / 2 : ℝ) - ε ≤ RCLike.re (μ (JLMS.clopenIndicator q.cell
          q.cell_isClopen q.cell_isCompact))} :=
      isClosed_le continuous_const (RCLike.continuous_re.comp (WeakDual.eval_continuous _))
    apply rankedWolfeFamily_closed_lower v (fun p => p.level.val) univ L q.level.val
      hqR (Ordinal.zero_le _) _ hclosed
    intro r hr hrq
    obtain ⟨hp, hU, hdiag, hmass⟩ := hleaf r hr hrq
    exact wolfe_re_indicator_le_of_outside M (wolfeOperatorRow R r.point)
      (r.bandCell_isClopen hθ (a n) hp) (r.bandCell_isCompact hθ (a n) hp)
      q.cell_isClopen q.cell_isCompact hU hqtop hdiag hmass

end Posets
