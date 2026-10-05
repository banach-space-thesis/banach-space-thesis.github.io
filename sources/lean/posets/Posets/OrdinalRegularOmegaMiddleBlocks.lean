import Posets.OrdinalIdealTransportSingularReplication
import JLMS.OrdinalSpacePowerSquare

/-! Qualitative replication and multiplication of the actual κ^ω model.
The base is any infinite initial ordinal; regularity is not required.
No bounds uniform in a varying exponent are asserted here. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance omegaMiddleBlocksEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance omegaMiddleBlocksEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance omegaMiddleBlocksSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance omegaMiddleBlocksSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

abbrev OrdinalOmegaMiddleEndpoint (𝕜 : Type) [RCLike 𝕜] (c : Cardinal.{0}) :=
  ↥(ordinalEndpointZero 𝕜 (c.ord ^ Ordinal.omega0))

theorem ordinalOmegaMiddle_base_infinite (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c) :
    Ordinal.omega0 ≤ c.ord ^ Ordinal.omega0 :=
  ordinalInitialPower_infinite c hc _ Ordinal.one_lt_omega0.le

theorem ordinalOmegaMiddle_base_card (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c) :
    (c.ord ^ Ordinal.omega0).card ≤ c := by
  have h := Ordinal.card_opow_le_of_omega0_le_left
    (Cardinal.omega0_le_ord.mpr hc) (Ordinal.omega0 : Ordinal.{0})
  simpa only [Cardinal.card_ord, Ordinal.card_omega0, max_eq_left hc] using h

def ordinalOmegaMiddleEndpointReplication (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c) :
    OrdinalOmegaMiddleEndpoint 𝕜 c ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord => OrdinalOmegaMiddleEndpoint 𝕜 c) :=
  Classical.choice (nonempty_ordinalEndpointZeroPowerReplication c hc Ordinal.omega0
    (Ordinal.nat_lt_omega0 2).le (by simpa only [Ordinal.card_omega0] using hc))

def ordinalOmegaMiddleEndpointSmallerReplication (c : Cardinal.{0})
    (hc : Cardinal.aleph0 ≤ c) (γ : Ordinal.{0})
    (hγ : Ordinal.omega0 ≤ γ) (hcard : γ.card ≤ c) :
    OrdinalOmegaMiddleEndpoint 𝕜 c ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio γ => OrdinalOmegaMiddleEndpoint 𝕜 c) := by
  letI : Infinite (Set.Iio c.ord) := ordinalIioInfinite _ (Cardinal.omega0_le_ord.mpr hc)
  letI : Infinite (Set.Iio γ) := ordinalIioInfinite _ hγ
  apply cZeroSum_smallerReplication _ (ordinalOmegaMiddleEndpointReplication c hc)
  simpa only [Ordinal.mk_Iio_ordinal, Cardinal.card_ord] using Cardinal.lift_le.mpr hcard

def ordinalOmegaMiddleConstantSumEquiv (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{0}) (hγ : Ordinal.omega0 ≤ γ) (hcard : γ.card ≤ c)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (e : X ≃L[𝕜] OrdinalOmegaMiddleEndpoint 𝕜 c) :
    CZeroSum 𝕜 (fun _ : Set.Iio γ => X) ≃L[𝕜] OrdinalOmegaMiddleEndpoint 𝕜 c :=
  (CZeroSum.congrRight (fun _ => e) (norm_nonneg _) (norm_nonneg _)
    (fun _ => le_rfl) (fun _ => le_rfl)).trans
      (ordinalOmegaMiddleEndpointSmallerReplication c hc γ hγ hcard).symm

def ordinalOmegaMiddleEndpointMultiplyEquiv (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (α γ : Ordinal.{0}) (hα : Ordinal.omega0 ≤ α) (hγ : Ordinal.omega0 ≤ γ)
    (hcard : γ.card ≤ c) (habs : γ = α ∨ γ + α = α)
    (e : ordinalEndpointZero 𝕜 α ≃L[𝕜] OrdinalOmegaMiddleEndpoint 𝕜 c) :
    ordinalEndpointZero 𝕜 (α * γ) ≃L[𝕜] OrdinalOmegaMiddleEndpoint 𝕜 c :=
  (ordinalEndpointZeroMultipleSumEquiv α γ hα hγ habs).trans
    (ordinalOmegaMiddleConstantSumEquiv c hc γ hγ hcard e)

def ordinalOmegaMiddleEndpointSuccessorEquiv (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (β : Ordinal.{0}) (hβ : 1 ≤ β)
    (e : ordinalEndpointZero 𝕜 (c.ord ^ β) ≃L[𝕜] OrdinalOmegaMiddleEndpoint 𝕜 c) :
    ordinalEndpointZero 𝕜 (c.ord ^ Order.succ β) ≃L[𝕜] OrdinalOmegaMiddleEndpoint 𝕜 c :=
  (ordinalEndpointZeroPowerSuccessorSum c hc β hβ).trans
    (ordinalOmegaMiddleConstantSumEquiv c hc c.ord (Cardinal.omega0_le_ord.mpr hc)
      (by rw [Cardinal.card_ord]) e)

end Posets
