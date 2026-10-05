import Posets.OrdinalIdealTransportRepeatedFactorization
import JLMS.OrdinalSpaceInitialInfiniteReduction

/-! Actual Type₀ repeated-block models below the square of an uncountable
initial ordinal. The index cardinal is strictly smaller than the base. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

local instance smallQuotientFunctionGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance smallQuotientFunctionSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance smallQuotientEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance smallQuotientEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

/-- The ordinary ordinal underlying the block index is represented in Type₀. -/
def initialOrdinalInfiniteQuotientSumEquiv
    {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c)
    (α : Ordinal.{0}) (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α ≤ c.ord * c.ord) :
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
    {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{0}} (hhi : α < c.ord * c.ord) :
    Cardinal.mk (α / c.ord).toType < c := by
  rw [Cardinal.mk_toType, ← Cardinal.lt_ord]
  exact (Ordinal.div_lt (show c.ord ≠ 0 by
    exact ne_of_gt (Ordinal.omega0_pos.trans_le
      (by simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le)))).mpr hhi

theorem initialOrdinalInfiniteQuotient_index_infinite
    {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{0}} (hlo : c.ord * Ordinal.omega0 ≤ α) :
    Infinite (α / c.ord).toType := by
  apply Cardinal.infinite_iff.mpr
  rw [Cardinal.mk_toType]
  simpa only [Ordinal.card_omega0] using
    Ordinal.card_le_card (initialInfiniteQuotient_omega_le c hu.le α hlo)

/-- This uses the actual scalar c₀ dichotomy on the smaller index cardinal. -/
theorem initialOrdinalInfiniteQuotient_hasUPFP_of_scalar
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{0}} (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α < c.ord * c.ord)
    (hs : HasUPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : (α / c.ord).toType => 𝕜))) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) := by
  letI := initialOrdinalInfiniteQuotient_index_infinite hu hlo
  exact (smallRepeatedRegularOrdinal_hasUPFP_of_scalar hc hu
    (initialOrdinalInfiniteQuotient_index_small hu hhi) hs).of_equiv
      (initialOrdinalInfiniteQuotientSumEquiv hu α hlo hhi.le).symm

end Posets
