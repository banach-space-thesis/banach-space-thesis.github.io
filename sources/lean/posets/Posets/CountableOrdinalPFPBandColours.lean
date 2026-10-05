import Posets.CountableOrdinalPFPBandCells
import Posets.CountableOrdinalPFPCanonicalFamily
import Posets.WolfeRankedTransport

/-! A finite colour records both a small ancestor band and one of the two
operators whose real diagonal is at least one half. Finite-colour pruning
retains the original ordinal rank and the original root. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}

def ordinalTowerBandColour (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (a : ℕ → Iic γ) (n : ℕ) (b : Bool) (ε : ℝ) : Set (OrdinalTowerNode θ γ) :=
  {p | wolfeMass M (wolfeOperatorRow T p.point) (p.bandCell (a (n+1)) \ p.bandCell (a n)) < ε ∧
    wolfeMass M (wolfeOperatorRow S p.point) (p.bandCell (a (n+1)) \ p.bandCell (a n)) < ε ∧
    ∃ hp : p.level.val ≤ (a n).val,
      (1 / 2 : ℝ) ≤ RCLike.re (wolfeOperatorRow (if b then T else S) p.point
        (JLMS.clopenIndicator (p.bandCell (a n)) (p.bandCell_isClopen hθ (a n) hp)
          (p.bandCell_isCompact hθ (a n) hp)))}

theorem ordinalTowerNode_exists_band_colour (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) (p : OrdinalTowerNode θ γ) (hp0 : p.level.val = 0) :
    ∃ i : Fin N × Bool, p ∈ ordinalTowerBandColour hθ M T S a i.1.val i.2 ε := by
  obtain ⟨n, hn, hT, hS⟩ := wolfeOperatorRows_small_band M T S
    (fun n => p.bandCell (a n)) ((p.bandCell_monotone hθ).comp ha) p.point hN
  have hp : p.level.val ≤ (a n).val := by rw [hp0]; exact Ordinal.zero_le _
  have hd := wolfeOperatorRows_diagonal_dichotomy T S hTS
    (p.bandCell_isClopen hθ (a n) hp) (p.bandCell_isCompact hθ (a n) hp)
    (p.point_mem_bandCell hθ (a n) hp)
  rcases hd with hd | hd
  · exact ⟨(⟨n, hn⟩, true), hT, hS, hp, hd⟩
  · exact ⟨(⟨n, hn⟩, false), hT, hS, hp, hd⟩

theorem ordinalTower_exists_coloured_band
    (hcθ : θ.card ≤ Cardinal.aleph0) (hcγ : γ.card ≤ Cardinal.aleph0)
    (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) (p : OrdinalTowerNode θ γ) :
    ∃ i : Fin N × Bool,
      p ∈ rankedWolfeFamily (OrdinalTowerNode.toWolfeNode (wolfeDirac (𝕜 := 𝕜)))
        (fun q => q.level.val) univ (ordinalTowerBandColour hθ M T S a i.1.val i.2 ε) p.level.val := by
  let v : OrdinalTowerNode θ γ → WolfeNode 𝕜 (Iic θ) :=
    OrdinalTowerNode.toWolfeNode (wolfeDirac (𝕜 := 𝕜) (K := Iic θ))
  let L : Fin N × Bool → Set (OrdinalTowerNode θ γ) :=
    fun i => ordinalTowerBandColour hθ M T S a i.1.val i.2 ε
  have hp := ordinalTowerNode_mem_rankedWolfeFamily hcθ hcγ hθ
    (wolfeDirac (𝕜 := 𝕜)) wolfeDirac_continuous p.level.val p rfl
  have hL : p ∈ rankedWolfeFamily v (fun q => q.level.val) univ (⋃ i, L i) p.level.val := by
    apply rankedWolfeFamily_mono_zero_leaves v (fun q => q.level.val) univ (L := univ) _ _ hp
    intro q _ hq _
    obtain ⟨i, hi⟩ := ordinalTowerNode_exists_band_colour hθ M T S hTS a ha hN q hq
    exact mem_iUnion.mpr ⟨i, hi⟩
  rw [rankedWolfeFamily_iUnion v (fun q => q.level.val) univ L] at hL
  exact mem_iUnion.mp hL

end Posets
