import Posets.OrdinalIdealTransportRegularFactorization
import JLMS.OrdinalSpaceEndpointZeroBounded

/-! Uniformly bounded factorisations for regular uncountable initial ordinals.
The maps are the actual selected ordinal copies; the estimates are independent
of both the cardinal and the operator. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

theorem norm_ordinalEndpointZeroProjection_apply_le (α : Ordinal.{0})
    (f : OrdinalC 𝕜 α) : ‖ordinalEndpointZeroProjection α f‖ ≤ 2 * ‖f‖ := by
  change ‖(ordinalEndpointZeroProjection α f).val‖ ≤ _
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg f))).mpr
  intro x
  change ‖f x - f ⟨α, Ordinal.zero_le _, le_rfl⟩ * 1‖ ≤ _
  rw [mul_one]
  have hx := f.norm_coe_le_norm x
  have ht := f.norm_coe_le_norm ⟨α, Ordinal.zero_le _, le_rfl⟩
  exact (norm_sub_le _ _).trans (by linarith)
theorem exists_loyWillis_zeroEndpoint_bounded_compression
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (S : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : S ∈ loyWillisZeroEndpointSubspace hc hu) :
    ∃ L R : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ L.comp (S.comp R) = 0 ∧
      (∀ f, R f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 := by
  obtain ⟨β, hβ, g, hg, hgtop, hgb, hzero⟩ :=
    exists_loyWillis_zeroEndpoint_tail_rows hc hu S hS
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


theorem initialOrdinal_factorsIdentityWith_of_jump_bound
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hjump : (1:ℝ)/2 ≤ ‖initialEndpointJump (𝕜 := 𝕜) hc hu T‖) :
    FactorsIdentityWith T (OrdinalC 𝕜 c.ord) 16 := by
  let a : 𝕜 := initialEndpointJump (𝕜 := 𝕜) hc hu T
  let U := T - a • ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)
  have hU : U ∈ loyWillisSubspace hc hu := sub_jump_smul_id_mem_loyWillisSubspace hc hu T
  let f := loyWillisEndpointColumn hc hu U hU
  let S := U - ordinalEndpointRankOne c.ord f
  have hS : S ∈ loyWillisZeroEndpointSubspace hc hu := by
    refine ⟨loyWillis_sub_endpointRankOne_mem hc hu U hU, ?_⟩
    change ordinalOperatorMatrix c.ord S ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0
    exact loyWillis_sub_endpointRankOne_zero_column hc hu U hU _
  obtain ⟨L, R, hLR, hLSR, hRtop, hL, hR⟩ := exists_loyWillis_zeroEndpoint_bounded_compression hc hu S hS
  have hSR (x : OrdinalC 𝕜 c.ord) : S (R x) = T (R x) - a • R x := by
    ext y
    change (T (R x) y - a * R x y) - R x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ * f y = _
    rw [hRtop, zero_mul, sub_zero]
    rfl
  have hcompression (x : OrdinalC 𝕜 c.ord) : L (T (R x)) = a • x := by
    have hz := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) hLSR
    have hid := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) hLR
    change L (R x) = x at hid
    change L (S (R x)) = 0 at hz
    rw [hSR, map_sub, map_smul, hid] at hz
    exact sub_eq_zero.mp hz
  have hapos : 0 < ‖a‖ := lt_of_lt_of_le (by norm_num) hjump
  have ha : a ≠ 0 := norm_pos_iff.mp hapos
  have hainv : ‖a⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ hapos]
    linarith
  refine ⟨a⁻¹ • L, R, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change a⁻¹ • L (T (R x)) = x
    rw [hcompression, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · rw [norm_smul]
    calc
      ‖a⁻¹‖ * ‖L‖ * ‖R‖ ≤ (2 * 4) * 2 := by gcongr
      _ = 16 := by norm_num

theorem initialOrdinal_hasCPFP_sixteen {c : Cardinal.{0}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) :
    HasCPFP 𝕜 (OrdinalSpace 𝕜 c.ord) 16 := by
  intro T
  by_cases hT : (1:ℝ)/2 ≤ ‖initialEndpointJump (𝕜 := 𝕜) hc hu T‖
  · exact Or.inl (initialOrdinal_factorsIdentityWith_of_jump_bound hc hu T hT)
  · right
    apply initialOrdinal_factorsIdentityWith_of_jump_bound hc hu
    rw [map_sub, initialEndpointJump_id]
    have htri := norm_add_le (initialEndpointJump (𝕜 := 𝕜) hc hu T)
      (1 - initialEndpointJump (𝕜 := 𝕜) hc hu T)
    rw [add_sub_cancel, norm_one] at htri
    linarith

theorem initialOrdinal_hasUPFP {c : Cardinal.{0}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) : HasUPFP 𝕜 (OrdinalSpace 𝕜 c.ord) :=
  ⟨16, by norm_num, initialOrdinal_hasCPFP_sixteen hc hu⟩

end Posets



