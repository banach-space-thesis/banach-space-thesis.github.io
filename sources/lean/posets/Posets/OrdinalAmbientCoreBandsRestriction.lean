import Posets.OrdinalAmbientCoreBandsImage

/-! Restricting an ambient band colour to one actual upper ceiling fiber.
All moving-cell estimates are asserted only at the original leaves. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
variable {θ γ : Ordinal.{u}}

def ordinalAmbientCeilingCell (e : Iic θ → K) (β : Ordinal.{u}) (x : Iic θ) : Set K :=
  e '' ordinalTowerCell θ (ordinalTowerLevel θ β)
    (ordinalCeiling (ordinalTowerLevel θ β) x.val)

/-- The same lower cell, indexed by an ambient point. It is empty off the
block, so this definition requires no choice of an inverse outside the range. -/
def ordinalAmbientCeilingCellAt (e : Iic θ → K) (β : Ordinal.{u}) (y : K) : Set K :=
  {z | ∃ x : Iic θ, e x = y ∧ z ∈ ordinalAmbientCeilingCell e β x}

omit [TopologicalSpace K] [T2Space K] in
theorem ordinalAmbientCeilingCellAt_apply (e : Iic θ → K) (he : Function.Injective e)
    (β : Ordinal.{u}) (x : Iic θ) :
    ordinalAmbientCeilingCellAt e β (e x) = ordinalAmbientCeilingCell e β x := by
  ext z
  constructor
  · rintro ⟨w, hw, hz⟩
    exact he hw ▸ hz
  · intro hz
    exact ⟨x, rfl, hz⟩

omit [TopologicalSpace K] [T2Space K] in
theorem ordinalAmbientCeilingCell_eq (e : Iic θ → K) (p : OrdinalTowerNode θ γ)
    (β : Iic γ) : ordinalAmbientCeilingCell e β.val p.point = ordinalAmbientBandCell e p β := rfl

theorem ordinalAmbientCore_restrict_closure (e : Iic θ → K) (he : IsOpenEmbedding e)
    (L U : Set (Iic θ)) (hU : IsOpen U) {x : Iic θ}
    (hx : x ∈ closure L) (hxU : x ∈ U) : e x ∈ closure (e '' (L ∩ U)) := by
  rw [ordinalAmbientCore_closure_image e he]
  exact mem_image_of_mem e (hU.closure_inter ⟨hx, hxU⟩)

/-- A leaf in the chosen upper fiber has a smaller compact clopen cell,
small variation on its complement in that fiber, and an actual indicator
value of norm at least one half for the selected global operator. -/
theorem ordinalAmbientBandLeaf_restrict_estimates
    (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (a : ℕ → Iic γ) (ha : Monotone a) (n : ℕ) (b : Bool) (ε : ℝ)
    (y : Ordinal.{u}) {x : Iic θ}
    (hx : x ∈ ordinalAmbientBandLeaves hθ e he M T S a n b ε)
    (hxU : x ∈ ordinalTowerCell θ (ordinalTowerLevel θ (a (n+1)).val) y) :
    let V := ordinalAmbientCeilingCell e (a n).val x
    let H := e '' ordinalTowerCell θ (ordinalTowerLevel θ (a (n+1)).val) y
    ∃ hV : IsClopen V, ∃ hcV : IsCompact V, V ⊆ H ∧
      wolfeMass M (wolfeOperatorRow (if b then T else S) (e x)) (H \ V) < ε ∧
      (1 / 2 : ℝ) ≤ ‖(if b then T else S) (JLMS.clopenIndicator V hV hcV) (e x)‖ := by
  obtain ⟨p, _, rfl, hcolour⟩ := hx
  obtain ⟨hT, hS, hp, hd⟩ := hcolour
  have hupper : p.bandCell (a (n+1)) =
      ordinalTowerCell θ (ordinalTowerLevel θ (a (n+1)).val) y := by
    change ordinalCeiling (ordinalTowerLevel θ (a (n+1)).val) p.point.val = y at hxU
    change ordinalTowerCell θ (ordinalTowerLevel θ (a (n+1)).val)
      (ordinalCeiling (ordinalTowerLevel θ (a (n+1)).val) p.point.val) = _
    rw [hxU]
  refine ⟨ordinalAmbientBandCell_isClopen hθ e he p (a n) hp,
    ordinalAmbientBandCell_isCompact hθ e he p (a n) hp, ?_, ?_, ?_⟩
  · change e '' p.bandCell (a n) ⊆ _
    rw [← hupper]
    exact image_mono (p.bandCell_monotone hθ (ha (Nat.le_succ n)))
  · have hm : wolfeMass M (wolfeOperatorRow (if b then T else S) (e p.point))
        (ordinalAmbientBandCell e p (a (n+1)) \ ordinalAmbientBandCell e p (a n)) < ε := by
      cases b
      · exact hS
      · exact hT
    change wolfeMass M (wolfeOperatorRow (if b then T else S) (e p.point))
      (e '' p.bandCell (a (n+1)) \ e '' p.bandCell (a n)) < ε at hm
    rw [hupper] at hm
    exact hm
  · exact hd.trans (RCLike.re_le_norm _)

theorem ordinalAmbientBandLeaf_image_estimates
    (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (a : ℕ → Iic γ) (ha : Monotone a) (n : ℕ) (b : Bool) (ε : ℝ)
    (y : Ordinal.{u}) {z : K}
    (hz : z ∈ e '' (ordinalAmbientBandLeaves hθ e he M T S a n b ε ∩
      ordinalTowerCell θ (ordinalTowerLevel θ (a (n+1)).val) y)) :
    let V := ordinalAmbientCeilingCellAt e (a n).val z
    let H := e '' ordinalTowerCell θ (ordinalTowerLevel θ (a (n+1)).val) y
    ∃ hV : IsClopen V, ∃ hcV : IsCompact V, V ⊆ H ∧
      wolfeMass M (wolfeOperatorRow (if b then T else S) z) (H \ V) < ε ∧
      (1 / 2 : ℝ) ≤ ‖(if b then T else S) (JLMS.clopenIndicator V hV hcV) z‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  dsimp only
  rw [ordinalAmbientCeilingCellAt_apply e he.injective]
  exact ordinalAmbientBandLeaf_restrict_estimates hθ e he M T S a ha n b ε y hx.1 hx.2

end Posets
