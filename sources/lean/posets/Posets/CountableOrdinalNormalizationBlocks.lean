import Posets.OrdinalMiddleClassificationBlocks
import Posets.SeparableMissingIdealCountEmbedding

/-! Constant countable sums over any countable ordinal power model.
These are actual isomorphisms from the proved endpoint-zero decompositions. -/
noncomputable section
open Set Topology
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

local instance countableNormalEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance countableNormalEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance countableNormalSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance countableNormalSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

def countablePowerEndpointReplication (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) :
    JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : Iio (Ordinal.omega0 : Ordinal.{0}) =>
        JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ)) := by
  have h := Classical.choice (JLMS.nonempty_ordinalEndpointZeroPowerReplication (𝕜 := 𝕜)
    Cardinal.aleph0 le_rfl δ hδ hcδ)
  rw [Cardinal.ord_aleph0] at h
  exact h

def countablePowerConstantSumEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (e : X ≃L[𝕜] JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ)) :
    JLMS.CZeroSum 𝕜 (fun _ : Iio (Ordinal.omega0 : Ordinal.{0}) => X) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ) :=
  (JLMS.CZeroSum.congrRight (fun _ => e) (norm_nonneg _) (norm_nonneg _)
    (fun _ => le_rfl) (fun _ => le_rfl)).trans (countablePowerEndpointReplication δ hδ hcδ).symm

def countablePowerEndpointMultiplyEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) (κ γ : Ordinal.{0})
    (hκ : Ordinal.omega0 ≤ κ) (hγ : Ordinal.omega0 ≤ γ)
    (hcγ : γ.card ≤ Cardinal.aleph0) (habs : γ = κ ∨ γ + κ = κ)
    (e : JLMS.ordinalEndpointZero 𝕜 κ ≃L[𝕜] JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ)) :
    JLMS.ordinalEndpointZero 𝕜 (κ * γ) ≃L[𝕜] JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ δ) :=
  (JLMS.ordinalEndpointZeroMultipleSumEquiv κ γ hκ hγ habs).trans
    ((JLMS.CZeroSum.reindex (𝕜 := 𝕜)
      (E := fun _ : Iio γ => ↥(JLMS.ordinalEndpointZero 𝕜 κ))
      (ordinalCountableIioEquiv γ hγ hcγ)).toContinuousLinearEquiv.trans
        (countablePowerConstantSumEquiv δ hδ hcδ e))

theorem countableNormal_power_infinite {δ : Ordinal.{0}} (hδ : 1 ≤ δ) :
    Ordinal.omega0 ≤ Ordinal.omega0 ^ δ := by
  simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos hδ

end Posets
