import Posets.OrdinalIdealTransportLowRank
import JLMS.OrdinalSpacePowerSquare

/-! Constant c₀ sums of the middle ordinal model collapse to that model.
The equal-factor case of Kislyakov's multiple-sum equivalence includes the
critical doubling of the exponent ω. -/
noncomputable section
open Set Topology
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

local instance middleEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance middleEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance middleSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance middleSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

abbrev OrdinalMiddleEndpoint (𝕜 : Type) [RCLike 𝕜] :=
  ↥(JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})))

def ordinalMiddleEndpointReplication : OrdinalMiddleEndpoint 𝕜 ≃L[𝕜]
    JLMS.CZeroSum 𝕜 (fun _ : Iio (Ordinal.omega0 : Ordinal.{0}) => OrdinalMiddleEndpoint 𝕜) := by
  have h := Classical.choice (JLMS.nonempty_ordinalEndpointZeroPowerReplication (𝕜 := 𝕜)
    Cardinal.aleph0 le_rfl (Ordinal.omega0 : Ordinal.{0})
    ((Ordinal.nat_lt_omega0 2).le) (by simp))
  rw [Cardinal.ord_aleph0] at h
  exact h

def ordinalMiddleConstantSumEquiv {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (e : X ≃L[𝕜] OrdinalMiddleEndpoint 𝕜) :
    JLMS.CZeroSum 𝕜 (fun _ : Iio (Ordinal.omega0 : Ordinal.{0}) => X) ≃L[𝕜]
      OrdinalMiddleEndpoint 𝕜 :=
  (JLMS.CZeroSum.congrRight (fun _ => e) (norm_nonneg _) (norm_nonneg _)
    (fun _ => le_rfl) (fun _ => le_rfl)).trans ordinalMiddleEndpointReplication.symm

def ordinalCountableIioEquiv (γ : Ordinal.{0}) (hγ : Ordinal.omega0 ≤ γ)
    (hc : γ.card ≤ Cardinal.aleph0) : Iio Ordinal.omega0 ≃ Iio γ := by
  letI : Infinite (Iio γ) := JLMS.ordinalIioInfinite γ hγ
  letI : Infinite (Iio (Ordinal.omega0 : Ordinal.{0})) := JLMS.ordinalIioInfinite _ le_rfl
  letI : Countable (Iio γ) := Cardinal.mk_le_aleph0_iff.mp (by
    rw [Ordinal.mk_Iio_ordinal]
    exact Cardinal.lift_le_aleph0.mpr hc)
  letI : Countable (Iio (Ordinal.omega0 : Ordinal.{0})) := Cardinal.mk_le_aleph0_iff.mp (by
    rw [Ordinal.mk_Iio_ordinal, Ordinal.card_omega0, Cardinal.lift_aleph0])
  exact Classical.choice nonempty_equiv_of_countable

def ordinalMiddleEndpointMultiplyEquiv (κ γ : Ordinal.{0})
    (hκ : Ordinal.omega0 ≤ κ) (hγ : Ordinal.omega0 ≤ γ)
    (hc : γ.card ≤ Cardinal.aleph0) (habs : γ = κ ∨ γ + κ = κ)
    (e : JLMS.ordinalEndpointZero 𝕜 κ ≃L[𝕜] OrdinalMiddleEndpoint 𝕜) :
    JLMS.ordinalEndpointZero 𝕜 (κ * γ) ≃L[𝕜] OrdinalMiddleEndpoint 𝕜 :=
  (JLMS.ordinalEndpointZeroMultipleSumEquiv κ γ hκ hγ habs).trans
    ((JLMS.CZeroSum.reindex (𝕜 := 𝕜)
      (E := fun _ : Iio γ => ↥(JLMS.ordinalEndpointZero 𝕜 κ))
      (ordinalCountableIioEquiv γ hγ hc)).toContinuousLinearEquiv.trans
        (ordinalMiddleConstantSumEquiv e))

def ordinalMiddleEndpointSuccessorEquiv (β : Ordinal.{0}) (hβ : 1 ≤ β)
    (e : JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ β) ≃L[𝕜] OrdinalMiddleEndpoint 𝕜) :
    JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ Order.succ β) ≃L[𝕜]
      OrdinalMiddleEndpoint 𝕜 := by
  have h := JLMS.ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) Cardinal.aleph0 le_rfl β hβ
  rw [Cardinal.ord_aleph0] at h
  exact h.trans (ordinalMiddleConstantSumEquiv e)

end Posets
