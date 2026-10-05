/- Universe-polymorphic extension of the checked Posets OrdinalIdealTransportRegularCompression proof. The actual Banach spaces, maps and constants are retained. -/
import LPCK.GenericOrdinalRows
import JLMS.OrdinalSpaceEndpointZero

/-! Actual complemented copies annihilating zero-endpoint Loy–Willis operators. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
open JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

/-- A bounded projection onto the actual endpoint-zero subspace. -/
def ordinalEndpointZeroProjection (α : Ordinal.{u}) :
    OrdinalC 𝕜 α →L[𝕜] ordinalEndpointZero 𝕜 α :=
  (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α) -
    (ContinuousMap.evalCLM 𝕜 (⟨α, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval α)).smulRight
      (ContinuousMap.const _ 1)).codRestrict (ordinalEndpointZero 𝕜 α) (by
        intro f
        change f ⟨α, Ordinal.zero_le _, le_rfl⟩ -
          f ⟨α, Ordinal.zero_le _, le_rfl⟩ * 1 = 0
        simp)

@[simp] theorem ordinalEndpointZeroProjection_subtype (α : Ordinal.{u})
    (f : ordinalEndpointZero 𝕜 α) : ordinalEndpointZeroProjection α f.val = f := by
  apply Subtype.ext
  ext x
  change f.val x - f.val ⟨α, Ordinal.zero_le _, le_rfl⟩ * 1 = f.val x
  have hf : f.val ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0 := f.property
  rw [hf, zero_mul, sub_zero]

/-- The selected copy is complemented, annihilates S after compression, and
its input functions vanish at the endpoint. -/
theorem exists_loyWillis_zeroEndpoint_compression
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (S : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : S ∈ loyWillisZeroEndpointSubspace hc hu) :
    ∃ L R : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ L.comp (S.comp R) = 0 ∧
      (∀ f, R f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) := by
  obtain ⟨β, hβ, g, hg, hgtop, hgb, hzero⟩ :=
    exists_loyWillis_zeroEndpoint_tail_rows hc hu S hS
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
  let e := ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) c.ord hκ
  let A : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    (ordinalCeilingExtension c.ord g hg.monotone hgtop).comp
      ((ordinalEndpointZero 𝕜 c.ord).subtypeL.comp e.toContinuousLinearMap)
  let R : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    (ContinuousLinearMap.id 𝕜 _ - ordinalHeadProjection c.ord β).comp A
  let L : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    e.symm.toContinuousLinearMap.comp
      ((ordinalEndpointZeroProjection c.ord).comp (ordinalTailPrecompose c.ord g))
  have hrestriction (f : OrdinalC 𝕜 c.ord) :
      ordinalTailPrecompose c.ord g (R f) = (e f).val := by
    ext x
    change A f (g x) - ordinalHeadProjection c.ord β (A f) (g x) = (e f).val x
    rw [ordinalHeadProjection_apply, if_neg (not_le_of_gt (hgb x)), sub_zero]
    change (e f).val (ordinalCeiling c.ord g (g x)) = (e f).val x
    rw [ordinalCeiling_apply_image c.ord g hg hgtop]
  refine ⟨L, R, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    change e.symm (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g (R f))) = f
    rw [hrestriction, ordinalEndpointZeroProjection_subtype, e.symm_apply_apply]
  · apply ContinuousLinearMap.ext
    intro f
    have hz : ordinalTailPrecompose c.ord g (S (R f)) = 0 := by
      ext x
      exact hzero (A f) x
    change e.symm (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g (S (R f)))) = 0
    rw [hz, map_zero, map_zero]
  · intro f
    change A f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ -
      ordinalHeadProjection c.ord β (A f) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0
    rw [ordinalHeadProjection_apply, if_neg (not_le_of_gt hβ), sub_zero]
    have hcceil : ordinalCeiling c.ord g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
        ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
      simpa only [hgtop] using ordinalCeiling_apply_image c.ord g hg hgtop ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
    change (e f).val (ordinalCeiling c.ord g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) = 0
    rw [hcceil]
    exact (e f).property

end LPCK.GenericOrdinal

