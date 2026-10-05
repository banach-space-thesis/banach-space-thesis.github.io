import Posets.CountableOrdinalNormalizationBlocks

/-! Finite multiples and short remainders of a countable exponent have
the same endpoint-zero model. This generalises the checked middle case. -/
noncomputable section
open Set Topology
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

local instance countableNormalPowerEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance countableNormalPowerEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance

def countablePowerEndpointMultipleEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) (n : ℕ) :
    JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal.{0}))) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ) := by
  induction n with
  | zero =>
      rw [show ((0+1 : ℕ) : Ordinal.{0}) = 1 by norm_num, mul_one]
  | succ n ih =>
      have hlo : Ordinal.omega0 ^ δ ≤ Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal)) :=
        Ordinal.opow_le_opow_right Ordinal.omega0_pos
          (Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos n))
      have habs : Ordinal.omega0 ^ δ = Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal)) ∨
          Ordinal.omega0 ^ δ + Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal)) =
          Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal)) := by
        rcases hlo.eq_or_lt with h | h
        · exact Or.inl h
        · exact Or.inr (Ordinal.principal_add_iff_add_left_eq_self.mp
            (Ordinal.principal_add_omega0_opow _) _ h)
      have he : Ordinal.omega0 ^ (δ * ((n+1+1 : ℕ) : Ordinal.{0})) =
          Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal)) * Ordinal.omega0 ^ δ := by
        rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Ordinal.opow_add]
      exact (JLMS.ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
        (countablePowerEndpointMultiplyEquiv δ hδ hcδ _ _
          ((countableNormal_power_infinite (one_le_two.trans hδ)).trans hlo)
          (countableNormal_power_infinite (one_le_two.trans hδ))
          (omega_power_card_le_aleph0 hcδ) habs ih)

def countablePowerEndpointMultipleAddEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) (n : ℕ) (ρ : Ordinal.{0}) (hρ : ρ < δ) :
    JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal.{0}) + ρ)) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ) := by
  by_cases hz : ρ = 0
  · subst ρ
    rw [add_zero]
    exact countablePowerEndpointMultipleEquiv δ hδ hcδ n
  · have hlo : δ ≤ δ * ((n+1 : ℕ) : Ordinal.{0}) :=
      Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos n)
    have hpow : Ordinal.omega0 ^ ρ < Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal.{0})) :=
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hρ.trans_le hlo)
    have habs : Ordinal.omega0 ^ ρ + Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal.{0})) =
        Ordinal.omega0 ^ (δ * ((n+1 : ℕ) : Ordinal.{0})) :=
      Ordinal.principal_add_iff_add_left_eq_self.mp (Ordinal.principal_add_omega0_opow _) _ hpow
    exact (JLMS.ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
      (Ordinal.opow_add Ordinal.omega0 (δ * ((n+1 : ℕ) : Ordinal.{0})) ρ)).toContinuousLinearEquiv.trans
        (countablePowerEndpointMultiplyEquiv δ hδ hcδ _ _
          (countableNormal_power_infinite ((one_le_two.trans hδ).trans hlo))
          (countableNormal_power_infinite (Order.one_le_iff_pos.mpr (Ordinal.pos_iff_ne_zero.mpr hz)))
          (omega_power_card_le_aleph0 ((Ordinal.card_le_card hρ.le).trans hcδ))
          (Or.inr habs) (countablePowerEndpointMultipleEquiv δ hδ hcδ n))

def countablePowerEndpointBandEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) (β : Ordinal.{0}) (hlo : δ ≤ β)
    (hhi : β < δ * Ordinal.omega0) :
    JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ β) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ) := by
  refine Classical.choice ?_
  have hδ0 : δ ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : Ordinal.{0}) < 2) hδ).ne'
  have hdiv : β / δ < Ordinal.omega0 := (Ordinal.div_lt hδ0).mpr hhi
  have hpos : 0 < β / δ := (Ordinal.div_pos hδ0).mpr hlo
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hdiv
  have hnpos : 0 < n := by
    have : (0 : Ordinal.{0}) < (n : Ordinal) := by simpa only [← hn] using hpos
    exact_mod_cast this
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  have he : β = δ * ((m+1 : ℕ) : Ordinal) + β % δ := by
    rw [← hn]
    exact (Ordinal.div_add_mod β δ).symm
  exact ⟨(JLMS.ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
    (congrArg (fun b => Ordinal.omega0 ^ b) he)).toContinuousLinearEquiv.trans
      (countablePowerEndpointMultipleAddEquiv δ hδ hcδ m (β % δ) (Ordinal.mod_lt β hδ0))⟩

end Posets
