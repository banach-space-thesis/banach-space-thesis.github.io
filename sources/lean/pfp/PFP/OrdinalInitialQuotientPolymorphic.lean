import JLMS.OrdinalSpaceInitialInfiniteReduction
import JLMS.OrdinalSpaceEndpointZeroBounded

/-! Actual infinite-quotient c₀ block models in arbitrary ordinal and scalar universes. -/
noncomputable section
namespace Posets.UniverseInitialQuotient
universe u
open JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

local instance smallQuotientFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance smallQuotientFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance smallQuotientEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance smallQuotientEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

/-- The ordinary ordinal underlying the block index is represented in its original universe. -/
def initialOrdinalInfiniteQuotientSumEquiv
    {c : Cardinal.{u}} (hu : Cardinal.aleph0 < c)
    (α : Ordinal.{u}) (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α ≤ c.ord * c.ord) :
    OrdinalC 𝕜 α ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : (α / c.ord).toType => OrdinalC 𝕜 c.ord) := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
  let e := ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord hκ
  have he : ‖e.toContinuousLinearMap‖ ≤ 2 := ContinuousLinearMap.opNorm_le_bound _
    (by norm_num) (norm_ordinalSpaceEndpointZeroBoundedEquiv_le c.ord hκ)
  have hei : ‖e.symm.toContinuousLinearMap‖ ≤ 2 := ContinuousLinearMap.opNorm_le_bound _
    (by norm_num) (norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le c.ord hκ)
  exact (ordinalSpaceInitialInfiniteSumEquiv (𝕜 := 𝕜) c hu.le α hlo hhi).trans
    ((JLMS.CZeroSum.reindex (𝕜 := 𝕜)
      (E := fun _ : Set.Iio (α / c.ord) => ordinalEndpointZero 𝕜 c.ord)
      (Ordinal.enumIsoToType (α / c.ord)).symm.toEquiv).toContinuousLinearEquiv.trans
      (JLMS.CZeroSum.congrRight (fun _ => e.symm) (by norm_num) (by norm_num)
        (fun _ => hei) (fun _ => he)))

theorem initialOrdinalInfiniteQuotient_index_small
    {c : Cardinal.{u}} (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{u}} (hhi : α < c.ord * c.ord) :
    Cardinal.mk (α / c.ord).toType < c := by
  rw [Cardinal.mk_toType, ← Cardinal.lt_ord]
  exact (Ordinal.div_lt (show c.ord ≠ 0 by
    exact ne_of_gt (Ordinal.omega0_pos.trans_le
      (by simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le)))).mpr hhi

theorem initialOrdinalInfiniteQuotient_index_infinite
    {c : Cardinal.{u}} (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{u}} (hlo : c.ord * Ordinal.omega0 ≤ α) :
    Infinite (α / c.ord).toType := by
  apply Cardinal.infinite_iff.mpr
  rw [Cardinal.mk_toType]
  simpa only [Ordinal.card_omega0] using
    Ordinal.card_le_card (initialInfiniteQuotient_omega_le c hu.le α hlo)


end Posets.UniverseInitialQuotient

