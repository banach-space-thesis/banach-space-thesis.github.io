import Posets.SzlenkOrdinalBoundsFinite
import Posets.SzlenkOrdinalBoundsCZeroSum
import JLMS.OrdinalSpacePowerLimit

/-! The actual Szlenk upper bound Sz(C[0,ω^ω]) ≤ ω². The endpoint-zero
space is the genuine varying c₀ sum of finite-power ordinal blocks. -/
noncomputable section
open Set Topology
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

local instance boundEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance boundEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance boundSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance boundSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem ordinalFinitePowerEndpoint_szlenkBound_omega0 (n : ℕ) :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜
      (JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0}))))
      (Ordinal.omega0 : Ordinal.{0}) := by
  have hn : (1 : Ordinal.{0}) ≤ ((n+1 : ℕ) : Ordinal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hinf : Ordinal.omega0 ≤ Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0}) := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos hn
  exact (ordinalFinitePower_szlenkBound_omega0 (𝕜 := 𝕜) n).id_of_equiv
    (JLMS.ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) _ hinf).symm

theorem ordinalOmegaOmegaEndpoint_szlenkBound_omega0_sq :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜
      (JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0}))))
      (Ordinal.omega0 ^ (2 : Ordinal.{0})) := by
  let I := Set.Iio (Ordinal.omega0 : Ordinal.{0}).cof.ord
  let E : I → Type _ := fun ξ => ↥(JLMS.ordinalEndpointZero 𝕜
    (Ordinal.omega0 ^ Order.succ (JLMS.ordinalPowerBlockPredecessor Ordinal.omega0 ξ.val)))
  have hE : ∀ ξ, OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (E ξ))
      (Ordinal.omega0 : Ordinal.{0}) := by
    intro ξ
    have hs := JLMS.ordinalCofinalExponent_successor_lt Ordinal.omega0
      Ordinal.isSuccLimit_omega0 ξ.property
    rw [JLMS.ordinalPowerBlockPredecessor_spec] at hs
    have hp := (Order.lt_succ (JLMS.ordinalPowerBlockPredecessor Ordinal.omega0 ξ.val)).trans hs
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hp
    change OperatorSzlenkBound (ContinuousLinearMap.id 𝕜
      (JLMS.ordinalEndpointZero 𝕜
        (Ordinal.omega0 ^ Order.succ (JLMS.ordinalPowerBlockPredecessor Ordinal.omega0 ξ.val)))) _
    rw [hn, ← Ordinal.natCast_succ]
    exact ordinalFinitePowerEndpoint_szlenkBound_omega0 n
  let e : JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 E := by
    have e := JLMS.ordinalEndpointZeroPowerLimitSum (𝕜 := 𝕜)
      Cardinal.aleph0 le_rfl (Ordinal.omega0 : Ordinal.{0}) Ordinal.isSuccLimit_omega0
      (by simp : (Ordinal.omega0 : Ordinal.{0}).card ≤ Cardinal.aleph0)
    rw [Cardinal.ord_aleph0] at e
    exact e
  exact (cZeroSum_szlenkBound_omega0_sq hE).id_of_equiv e

theorem ordinalOmegaOmega_szlenkBound_omega0_sq :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜
      (OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0}))))
      (Ordinal.omega0 ^ (2 : Ordinal.{0})) := by
  have hinf : Ordinal.omega0 ≤ Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0}) := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
      Ordinal.one_lt_omega0.le
  exact ordinalOmegaOmegaEndpoint_szlenkBound_omega0_sq.id_of_equiv
    (JLMS.ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) _ hinf)

end Posets
