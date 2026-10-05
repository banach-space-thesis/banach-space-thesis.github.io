import Posets.OrdinalMiddleClassificationBlocks

/-! All powers ω^β with ω ≤ β < ω² have the same actual endpoint-zero
Banach space model. -/
noncomputable section
open Set Topology
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

local instance middlePowerEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance middlePowerEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance

theorem ordinalMiddle_omega_le_mul_succ (n : ℕ) :
    (Ordinal.omega0 : Ordinal.{0}) ≤ Ordinal.omega0 * ((n+1 : ℕ) : Ordinal) :=
  Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos n)

theorem ordinalMiddle_base_infinite :
    (Ordinal.omega0 : Ordinal.{0}) ≤ Ordinal.omega0 ^ Ordinal.omega0 := by
  simpa only [Ordinal.opow_one] using
    Ordinal.opow_le_opow_right Ordinal.omega0_pos Ordinal.one_lt_omega0.le

theorem ordinalMiddle_base_card :
    (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})).card ≤ Cardinal.aleph0 := by
  simpa only [Ordinal.card_omega0, max_self] using
    Ordinal.card_opow_le_of_omega0_le_left (le_refl (Ordinal.omega0 : Ordinal.{0})) Ordinal.omega0

def ordinalMiddleEndpointOmegaMultipleEquiv (n : ℕ) :
    JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal.{0})))
      ≃L[𝕜] OrdinalMiddleEndpoint 𝕜 := by
  induction n with
  | zero =>
      rw [show ((0+1 : ℕ) : Ordinal.{0}) = 1 by norm_num, mul_one]
  | succ n ih =>
      have hlo : Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0}) ≤
          Ordinal.omega0 ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) :=
        Ordinal.opow_le_opow_right Ordinal.omega0_pos (ordinalMiddle_omega_le_mul_succ n)
      have habs : Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0}) =
          Ordinal.omega0 ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) ∨
          Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0}) +
          Ordinal.omega0 ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) =
          Ordinal.omega0 ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) := by
        rcases hlo.eq_or_lt with h | h
        · exact Or.inl h
        · exact Or.inr (Ordinal.principal_add_iff_add_left_eq_self.mp
            (Ordinal.principal_add_omega0_opow _) _ h)
      have he : Ordinal.omega0 ^ (Ordinal.omega0 * ((n+1+1 : ℕ) : Ordinal.{0})) =
          Ordinal.omega0 ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) *
          Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0}) := by
        rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Ordinal.opow_add]
      exact (JLMS.ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
        (ordinalMiddleEndpointMultiplyEquiv _ _ (ordinalMiddle_base_infinite.trans hlo)
          ordinalMiddle_base_infinite ordinalMiddle_base_card habs ih)

def ordinalMiddleEndpointOmegaMultipleAddEquiv (n k : ℕ) :
    JLMS.ordinalEndpointZero 𝕜
      (Ordinal.omega0 ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal.{0}) + (k : Ordinal))) ≃L[𝕜]
        OrdinalMiddleEndpoint 𝕜 := by
  induction k with
  | zero =>
      rw [Nat.cast_zero, add_zero]
      exact ordinalMiddleEndpointOmegaMultipleEquiv (𝕜 := 𝕜) n
  | succ k ih =>
      rw [show ((k+1 : ℕ) : Ordinal.{0}) = Order.succ (k : Ordinal) from Ordinal.natCast_succ k,
        Ordinal.add_succ]
      apply ordinalMiddleEndpointSuccessorEquiv _ _ ih
      exact Ordinal.one_lt_omega0.le.trans ((ordinalMiddle_omega_le_mul_succ n).trans
        (Ordinal.le_add_right _ _))

def ordinalMiddleEndpointPowerEquiv (β : Ordinal.{0}) (hlo : Ordinal.omega0 ≤ β)
    (hhi : β < Ordinal.omega0 ^ (2 : Ordinal.{0})) :
    JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ β) ≃L[𝕜] OrdinalMiddleEndpoint 𝕜 := by
  refine Classical.choice ?_
  have hdiv : β / Ordinal.omega0 < Ordinal.omega0 :=
    (Ordinal.div_lt Ordinal.omega0_ne_zero).mpr (by
      simpa only [show (2 : Ordinal.{0}) = 1 + 1 by norm_num,
        Ordinal.opow_add, Ordinal.opow_one] using hhi)
  have hpos : 0 < β / Ordinal.omega0 :=
    (Ordinal.div_pos Ordinal.omega0_ne_zero).mpr hlo
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hdiv
  have hnpos : 0 < n := by
    have : (0 : Ordinal.{0}) < (n : Ordinal) := by simpa only [← hn] using hpos
    exact_mod_cast this
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt β Ordinal.omega0_ne_zero)
  have he : β = Ordinal.omega0 * ((m+1 : ℕ) : Ordinal) + (k : Ordinal) := by
    rw [← hn, ← hk]
    exact (Ordinal.div_add_mod β Ordinal.omega0).symm
  exact ⟨(JLMS.ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
    (congrArg (fun b => Ordinal.omega0 ^ b) he)).toContinuousLinearEquiv.trans
      (ordinalMiddleEndpointOmegaMultipleAddEquiv m k)⟩

end Posets
