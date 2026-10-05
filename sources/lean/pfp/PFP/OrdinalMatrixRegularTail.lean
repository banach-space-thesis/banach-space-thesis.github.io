import PFP.OrdinalRegularInitialQuantitative
import PFP.OrdinalMatrixSmallCodomain
/-! The regular-ordinal factorisation can be placed beyond any prescribed
cutoff, while its left factor annihilates functions constant on that tail. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

theorem exists_loyWillis_zeroEndpoint_tail_rows_above
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (S : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : S ∈ loyWillisZeroEndpointSubspace hc hu) (δ : Ordinal.{ordU}) (hδ : δ < c.ord) :
    ∃ β : Ordinal.{ordU}, β < c.ord ∧ δ ≤ β ∧
      ∃ g : C(OrdinalInterval c.ord, OrdinalInterval c.ord), StrictMono g ∧
        g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ ∧
        (∀ x, β < (g x).val) ∧
        (∀ f x, S (f - ordinalHeadProjection c.ord β f) (g x) = 0) := by
  obtain ⟨β₀, hβ₀, g₀, hg₀, hgtop₀, _, hzero₀⟩ :=
    exists_loyWillis_zeroEndpoint_tail_rows hc hu S hS
  let β := max β₀ δ
  have hβ : β < c.ord := max_lt hβ₀ hδ
  let g := ordinalTailLimitRowsSelector hu hβ g₀
  refine ⟨β, hβ, le_max_right _ _, g,
    ordinalTailLimitRowsSelector_strictMono hu hβ g₀ hg₀,
    ordinalTailLimitRowsSelector_endpoint hu hβ g₀ hgtop₀,
    ordinalTailLimitRowsSelector_above hu hβ g₀ hg₀, ?_⟩
  intro f x
  have hp : ordinalHeadProjection c.ord β₀ (f - ordinalHeadProjection c.ord β f) = 0 := by
    ext y
    by_cases hy : y.val ≤ β₀
    · have hyβ : y.val ≤ β := hy.trans (le_max_left _ _)
      simp [ordinalHeadProjection_apply, hy, hyβ]
    · simp [ordinalHeadProjection_apply, hy]
  have hz := hzero₀ (f - ordinalHeadProjection c.ord β f)
    (initialOrdinalTailLimitIndices hu hβ x)
  rw [hp, sub_zero] at hz
  exact hz

theorem exists_loyWillis_zeroEndpoint_bounded_tail_compression
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (S : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : S ∈ loyWillisZeroEndpointSubspace hc hu) (δ : Ordinal.{ordU}) (hδ : δ < c.ord) :
    ∃ L R : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ L.comp (S.comp R) = 0 ∧
      (∀ f, R f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 ∧
      (∀ f x, x.val ≤ δ → R f x = 0) ∧ (∀ f ∈ ordinalTailSpace c.ord δ, L f = 0) := by
  obtain ⟨β, hβ, hδβ, g, hg, hgtop, hgb, hzero⟩ :=
    exists_loyWillis_zeroEndpoint_tail_rows_above hc hu S hS δ hδ
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
  refine ⟨L, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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


  · intro f x hx
    change A f x - ordinalHeadProjection c.ord β (A f) x = 0
    simp [ordinalHeadProjection_apply, hx.trans hδβ]
  · intro f hf
    have hp : ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g f) = 0 := by
      apply Subtype.ext
      ext x
      change f (g x) - f (g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) * 1 = 0
      rw [hgtop, hf (g x) (hδβ.trans_lt (hgb x)), mul_one, sub_self]
    change e.symm (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g f)) = 0
    rw [hp, map_zero]

end Posets.UniverseRegularMatrix


