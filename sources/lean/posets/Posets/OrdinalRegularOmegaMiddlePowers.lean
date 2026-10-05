import Posets.OrdinalRegularOmegaMiddleBlocks

/-! Actual qualitative endpoint-zero equivalences for κ^β, ω ≤ β < ω². -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance omegaMiddlePowersEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance omegaMiddlePowersEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

theorem ordinalOmegaMiddle_omega_le_mul_succ (n : ℕ) :
    (Ordinal.omega0 : Ordinal.{0}) ≤ Ordinal.omega0 * ((n+1 : ℕ) : Ordinal) :=
  Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos n)

def ordinalOmegaMiddleEndpointOmegaMultipleEquiv (c : Cardinal.{0})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) :
    ordinalEndpointZero 𝕜 (c.ord ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal.{0})))
      ≃L[𝕜] OrdinalOmegaMiddleEndpoint 𝕜 c := by
  induction n with
  | zero =>
      rw [show ((0+1 : ℕ) : Ordinal.{0}) = 1 by norm_num, mul_one]
  | succ n ih =>
      have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc)
      have hlo : c.ord ^ Ordinal.omega0 ≤
          c.ord ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) :=
        Ordinal.opow_le_opow_right hκ (ordinalOmegaMiddle_omega_le_mul_succ n)
      have habs : c.ord ^ Ordinal.omega0 =
          c.ord ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) ∨
          c.ord ^ Ordinal.omega0 + c.ord ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) =
          c.ord ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) := by
        rcases hlo.eq_or_lt with h | h
        · exact Or.inl h
        · exact Or.inr (Ordinal.principal_add_iff_add_left_eq_self.mp
            (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) _) _ h)
      have he : c.ord ^ (Ordinal.omega0 * ((n+1+1 : ℕ) : Ordinal.{0})) =
          c.ord ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal)) * c.ord ^ Ordinal.omega0 := by
        rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Ordinal.opow_add]
      exact (ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
        (ordinalOmegaMiddleEndpointMultiplyEquiv c hc _ _
          ((ordinalOmegaMiddle_base_infinite c hc).trans hlo)
          (ordinalOmegaMiddle_base_infinite c hc) (ordinalOmegaMiddle_base_card c hc) habs ih)

def ordinalOmegaMiddleEndpointOmegaMultipleAddEquiv (c : Cardinal.{0})
    (hc : Cardinal.aleph0 ≤ c) (n k : ℕ) :
    ordinalEndpointZero 𝕜
      (c.ord ^ (Ordinal.omega0 * ((n+1 : ℕ) : Ordinal.{0}) + (k : Ordinal))) ≃L[𝕜]
        OrdinalOmegaMiddleEndpoint 𝕜 c := by
  induction k with
  | zero =>
      rw [Nat.cast_zero, add_zero]
      exact ordinalOmegaMiddleEndpointOmegaMultipleEquiv c hc n
  | succ k ih =>
      rw [show ((k+1 : ℕ) : Ordinal.{0}) = Order.succ (k : Ordinal) from Ordinal.natCast_succ k,
        Ordinal.add_succ]
      apply ordinalOmegaMiddleEndpointSuccessorEquiv c hc _ _ ih
      exact Ordinal.one_lt_omega0.le.trans ((ordinalOmegaMiddle_omega_le_mul_succ n).trans
        (Ordinal.le_add_right _ _))

def ordinalOmegaMiddleEndpointPowerEquiv (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (β : Ordinal.{0}) (hlo : Ordinal.omega0 ≤ β)
    (hhi : β < Ordinal.omega0 ^ (2 : Ordinal.{0})) :
    ordinalEndpointZero 𝕜 (c.ord ^ β) ≃L[𝕜] OrdinalOmegaMiddleEndpoint 𝕜 c := by
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
  exact ⟨(ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
    (congrArg (fun b => c.ord ^ b) he)).toContinuousLinearEquiv.trans
      (ordinalOmegaMiddleEndpointOmegaMultipleAddEquiv c hc m k)⟩

end Posets
