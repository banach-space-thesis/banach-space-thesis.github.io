import Posets.CountableOrdinalPFPBandSelection

/-! Equally spaced finite ancestor levels yield a norming band with any
prescribed ordinal width, at the cost of finitely many copies of that width. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}

def ordinalFiniteBandLevels (β γ : Ordinal.{u}) (n : ℕ) : Iic γ :=
  ⟨min (β * n) γ, show min (β * n) γ ≤ γ from min_le_right _ _⟩

theorem ordinalFiniteBandLevels_monotone (β γ : Ordinal.{u}) :
    Monotone (ordinalFiniteBandLevels β γ) := by
  intro m n hmn
  exact min_le_min_right γ (mul_le_mul_left'
    (show (m : Ordinal.{u}) ≤ (n : Ordinal.{u}) by exact_mod_cast hmn) β)

theorem ordinalFiniteBandLevels_eq {β γ : Ordinal.{u}} {n N : ℕ}
    (hn : n ≤ N) (hN : β * N ≤ γ) : (ordinalFiniteBandLevels β γ n).val = β * n := by
  exact min_eq_left ((mul_le_mul_left'
    (show (n : Ordinal.{u}) ≤ (N : Ordinal.{u}) by exact_mod_cast hn) β).trans hN)

theorem ordinalTower_exists_norming_band_length
    (hcθ : θ.card ≤ Cardinal.aleph0) (hcγ : γ.card ≤ Cardinal.aleph0)
    (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hN : ‖T‖ + ‖S‖ < N * ε)
    (p : OrdinalTowerNode θ γ) (β : Ordinal.{u}) (hβ : β * N ≤ p.level.val) :
    ∃ (b : Bool) (lower : Iic γ) (F : OrdinalTowerNormingBand M (if b then T else S) lower ε),
      F.top.level.val = lower.val + β ∧ F.top.cell ⊆ p.cell := by
  have hβγ : β * N ≤ γ := hβ.trans p.level.property
  obtain ⟨i, F, htop, hcell⟩ := ordinalTower_exists_norming_band hcθ hcγ hθ M T S hTS
    (ordinalFiniteBandLevels β γ) (ordinalFiniteBandLevels_monotone β γ) hε hN p (by
      intro n hn
      rw [ordinalFiniteBandLevels_eq (Nat.succ_le_of_lt hn) hβγ]
      exact (mul_le_mul_left' (by exact_mod_cast Nat.succ_le_of_lt hn) β).trans hβ)
  refine ⟨i.2, ordinalFiniteBandLevels β γ i.1.val, F, ?_, hcell⟩
  rw [congrArg Subtype.val htop,
    ordinalFiniteBandLevels_eq (Nat.succ_le_of_lt i.1.isLt) hβγ,
    ordinalFiniteBandLevels_eq i.1.isLt.le hβγ]
  change β * ((i.1.val + 1 : ℕ) : Ordinal.{u}) = β * (i.1.val : Ordinal.{u}) + β
  rw [Ordinal.natCast_succ, Ordinal.mul_succ]

end Posets
