/- Universe-polymorphic extension of Posets.OrdinalIdealTransportFamilyCompression. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalFamilyRows

/-! A single bounded pair of maps simultaneously compresses a countable
family of zero-endpoint Loy–Willis operators to zero. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
set_option synthInstance.maxHeartbeats 200000
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

theorem exists_loyWillis_zeroEndpoint_bounded_family_compression
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (S : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : ∀ n, S n ∈ loyWillisZeroEndpointSubspace hc hu) :
    ∃ L R : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ (∀ n, L.comp ((S n).comp R) = 0) ∧
      (∀ f, R f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 := by
  obtain ⟨β, hβ, g, hg, hgtop, hgb, hzero⟩ :=
    exists_loyWillis_zeroEndpoint_family_tail_rows hc hu S hS
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
  let e := ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord hκ
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
  refine ⟨L, R, ?_, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    change e.symm (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g (R f))) = f
    rw [hrestriction, ordinalEndpointZeroProjection_subtype, e.symm_apply_apply]
  · intro n
    apply ContinuousLinearMap.ext
    intro f
    have hz : ordinalTailPrecompose c.ord g (S n (R f)) = 0 := by
      ext x
      exact hzero n (A f) x
    change e.symm (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g (S n (R f)))) = 0
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

  · apply ContinuousLinearMap.opNorm_le_bound L (by norm_num : (0 : ℝ) ≤ 4)
    intro f
    have hread : ‖ordinalTailPrecompose c.ord g f‖ ≤ ‖f‖ := by
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      exact f.norm_coe_le_norm (g x)
    have hp := norm_ordinalEndpointZeroProjection_apply_le c.ord
      (ordinalTailPrecompose c.ord g f)
    have he := norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le c.ord hκ
      (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g f))
    change ‖e.symm (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g f))‖ ≤ _
    change ‖e.symm (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g f))‖ ≤ _ at he
    linarith
  · apply ContinuousLinearMap.opNorm_le_bound R (by norm_num : (0 : ℝ) ≤ 2)
    intro f
    apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg f))).mpr
    intro x
    change ‖A f x - ordinalHeadProjection c.ord β (A f) x‖ ≤ _
    rw [ordinalHeadProjection_apply]
    split_ifs with hx
    · simp only [sub_self, norm_zero]
      exact mul_nonneg (by norm_num) (norm_nonneg f)
    · rw [sub_zero]
      change ‖(e f).val (ordinalCeiling c.ord g x)‖ ≤ _
      exact ((e f).val.norm_coe_le_norm _).trans
        (norm_ordinalSpaceEndpointZeroBoundedEquiv_le c.ord hκ f)



end LPCK.GenericOrdinal




