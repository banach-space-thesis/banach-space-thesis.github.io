import Posets.CountableOrdinalPFPBandBounds
import Posets.WolfeRankedSelected

/-! Countable local norming families extracted from one ancestor band.
The base remembers the original leaf colour, so subsequent full-rank leaf
pruning preserves both the diagonal and the outside-mass bounds. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}

structure OrdinalTowerNormingBand (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ)) (lower : Iic γ) (ε : ℝ) where
  top : OrdinalTowerNode θ γ
  base : Set (OrdinalTowerNode θ γ)
  leaves : Set (OrdinalTowerNode θ γ)
  countable : base.Countable
  root_mem : top ∈ base
  rank : top ∈ rankedWolfeFamily (OrdinalTowerNode.toWolfeNode (wolfeOperatorRow T))
    (fun p => p.level.val) base leaves top.level.val
  cells : ∀ q ∈ base, q.cell ⊆ top.cell
  small : ∀ q ∈ base, wolfeMass M (wolfeOperatorRow T q.point)
    (rankedWolfeDescendantUnion (OrdinalTowerNode.toWolfeNode (wolfeOperatorRow T)) base q) < ε
  outside : ∀ q ∈ base, lower.val ≤ q.level.val →
    wolfeMass M (wolfeOperatorRow T q.point) (top.cell \ q.cell) ≤ ε
  diagonal : ∀ q ∈ base, lower.val ≤ q.level.val →
    (1 / 2 : ℝ) - ε ≤ RCLike.re (wolfeOperatorRow T q.point
      (JLMS.clopenIndicator q.cell q.cell_isClopen q.cell_isCompact))

theorem ordinalTower_exists_norming_band
    (hcθ : θ.card ≤ Cardinal.aleph0) (hcγ : γ.card ≤ Cardinal.aleph0)
    (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hN : ‖T‖ + ‖S‖ < N * ε) (p : OrdinalTowerNode θ γ)
    (hlevels : ∀ n < N, (a (n+1)).val ≤ p.level.val) :
    ∃ (i : Fin N × Bool)
      (F : OrdinalTowerNormingBand M (if i.2 then T else S) (a i.1.val) ε),
      F.top.level = a (i.1.val+1) ∧ F.top.cell ⊆ p.cell := by
  obtain ⟨i, hi⟩ := ordinalTower_exists_coloured_band hcθ hcγ hθ M T S hTS a ha hN p
  let d : OrdinalTowerNode θ γ → WolfeNode 𝕜 (Iic θ) :=
    OrdinalTowerNode.toWolfeNode (wolfeDirac (𝕜 := 𝕜))
  let L := ordinalTowerBandColour hθ M T S a i.1.val i.2 ε
  let B := rankedWolfeHereditaryBase d (fun q => q.level.val) univ L
  let R := if i.2 then T else S
  let v : OrdinalTowerNode θ γ → WolfeNode 𝕜 (Iic θ) :=
    OrdinalTowerNode.toWolfeNode (wolfeOperatorRow R)
  obtain ⟨top, htop, htopcell⟩ := rankedWolfeFamily_exists_lower d (fun q => q.level.val)
    univ L p.level.val hi (hlevels i.1.val i.1.isLt)
  have htlevel : top.level = a (i.1.val+1) := Subtype.ext
    (rankedWolfeFamily_base_height d (fun q => q.level.val) univ L _ htop).2
  have ht : top ∈ rankedWolfeFamily d (fun q => q.level.val) B L top.level.val := by
    rw [rankedWolfeFamily_restrict_hereditary]
    simpa only [htlevel] using htop
  have htR : top ∈ rankedWolfeFamily v (fun q => q.level.val) B L top.level.val :=
    rankedWolfeFamily_operator_rows (fun q : OrdinalTowerNode θ γ => q.point)
      (fun q => q.cell) (fun q => q.level.val) B L R top.level.val ht
  obtain ⟨C, hC, hCrank⟩ := rankedWolfeFamily_exists_countable_selection M v
    (fun q => q.level.val) B L (fun q _ => q.cell_nonempty) hε top.level.val htR
  have hb (q : OrdinalTowerNode θ γ) (hq : q ∈ C) (hlow : (a i.1.val).val ≤ q.level.val) :=
    ordinalTower_coloured_band_bounds hθ M T S a i.1.val i.2 ε top q htlevel
      (hC.cells q hq) hlow (hC.subset hq)
  let F : OrdinalTowerNormingBand M R (a i.1.val) ε :=
    { top := top
      base := C
      leaves := L
      countable := hC.countable
      root_mem := hC.root
      rank := hCrank
      cells := hC.cells
      small := hC.small
      outside := fun q hq hlow => (hb q hq hlow).1
      diagonal := fun q hq hlow => (hb q hq hlow).2 }
  exact ⟨i, F, htlevel, htopcell⟩

end Posets
