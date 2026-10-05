import PFP.OrdinalMatrixRegularTail
/-! Matched restriction and ceiling-extension factors for any cofinal
strictly increasing selector, with explicit uniform norm bounds. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

private theorem selector_omega_le {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c) :
    Ordinal.omega0 ≤ c.ord := by
  simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le

def ordinalSelectorLeft {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) :
    OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
  (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu)).symm.toContinuousLinearMap.comp
    ((ordinalEndpointZeroProjection c.ord).comp (ordinalTailPrecompose c.ord g))

def ordinalSelectorExtension {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hg : StrictMono g)
    (htop : g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) :
    OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
  (ordinalCeilingExtension c.ord g hg.monotone htop).comp
    ((ordinalEndpointZero 𝕜 c.ord).subtypeL.comp
      (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu)).toContinuousLinearMap)

def ordinalSelectorRight {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (τ : Ordinal.{ordU}) (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hg : StrictMono g)
    (htop : g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) :
    OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
  (ContinuousLinearMap.id 𝕜 _ - ordinalHeadProjection c.ord τ).comp
    (ordinalSelectorExtension hu g hg htop)

theorem ordinalSelectorRight_read {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (τ : Ordinal.{ordU}) (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hg : StrictMono g)
    (htop : g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩)
    (hτg : ∀ x, τ < (g x).val) (f : OrdinalC 𝕜 c.ord) :
    ordinalTailPrecompose c.ord g (ordinalSelectorRight hu τ g hg htop f) =
      (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu) f).val := by
  ext x
  change ordinalSelectorExtension hu g hg htop f (g x) -
    ordinalHeadProjection c.ord τ (ordinalSelectorExtension hu g hg htop f) (g x) = _
  rw [ordinalHeadProjection_apply, if_neg (not_le_of_gt (hτg x)), sub_zero]
  change (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu) f).val
    (ordinalCeiling c.ord g (g x)) = _
  rw [ordinalCeiling_apply_image c.ord g hg htop]

theorem ordinalSelectorLeft_right {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (τ : Ordinal.{ordU}) (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hg : StrictMono g)
    (htop : g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩)
    (hτg : ∀ x, τ < (g x).val) :
    (ordinalSelectorLeft hu g).comp (ordinalSelectorRight hu τ g hg htop) =
      ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro f
  change (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu)).symm
    (ordinalEndpointZeroProjection c.ord
      (ordinalTailPrecompose c.ord g (ordinalSelectorRight hu τ g hg htop f))) = f
  rw [ordinalSelectorRight_read hu τ g hg htop hτg f,
    ordinalEndpointZeroProjection_subtype, ContinuousLinearEquiv.symm_apply_apply]

theorem ordinalSelectorLeft_eq_zero_of_read_constant
    {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (f : OrdinalC 𝕜 c.ord) (h : ∀ x, f (g x) = f (g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩)) :
    ordinalSelectorLeft hu g f = 0 := by
  have hp : ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g f) = 0 := by
    apply Subtype.ext
    ext x
    change f (g x) - f (g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) * 1 = 0
    rw [h, mul_one, sub_self]
  change (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu)).symm
    (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g f)) = 0
  rw [hp, map_zero]

theorem ordinalSelectorRight_head_zero {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (τ : Ordinal.{ordU}) (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hg : StrictMono g) (htop)
    (f : OrdinalC 𝕜 c.ord) (x : OrdinalInterval c.ord) (hx : x.val ≤ τ) :
    ordinalSelectorRight hu τ g hg htop f x = 0 := by
  change ordinalSelectorExtension hu g hg htop f x -
    ordinalHeadProjection c.ord τ (ordinalSelectorExtension hu g hg htop f) x = 0
  rw [ordinalHeadProjection_apply, if_pos hx, sub_self]

theorem ordinalSelectorRight_endpoint_zero {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (τ : Ordinal.{ordU}) (hτ : τ < c.ord) (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hg : StrictMono g) (htop) (f : OrdinalC 𝕜 c.ord) :
    ordinalSelectorRight hu τ g hg htop f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 := by
  change ordinalSelectorExtension hu g hg htop f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ -
    ordinalHeadProjection c.ord τ (ordinalSelectorExtension hu g hg htop f)
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0
  rw [ordinalHeadProjection_apply, if_neg (not_le_of_gt hτ), sub_zero]
  have hcceil : ordinalCeiling c.ord g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
    simpa only [htop] using ordinalCeiling_apply_image c.ord g hg htop
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
  change (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu) f).val
    (ordinalCeiling c.ord g _) = 0
  rw [hcceil]
  exact (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu) f).property

theorem norm_ordinalSelectorLeft_le {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) : ‖ordinalSelectorLeft (𝕜 := 𝕜) hu g‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have hread : ‖ordinalTailPrecompose c.ord g f‖ ≤ ‖f‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    exact f.norm_coe_le_norm (g x)
  have hp := norm_ordinalEndpointZeroProjection_apply_le c.ord (ordinalTailPrecompose c.ord g f)
  have he := norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le c.ord (selector_omega_le hu)
    (ordinalEndpointZeroProjection c.ord (ordinalTailPrecompose c.ord g f))
  exact he.trans (by nlinarith)

theorem norm_ordinalSelectorRight_le {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c)
    (τ : Ordinal.{ordU}) (g : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hg : StrictMono g) (htop) : ‖ordinalSelectorRight (𝕜 := 𝕜) hu τ g hg htop‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg f))).mpr
  intro x
  change ‖ordinalSelectorExtension hu g hg htop f x -
    ordinalHeadProjection c.ord τ (ordinalSelectorExtension hu g hg htop f) x‖ ≤ _
  rw [ordinalHeadProjection_apply]
  split_ifs with hx
  · simp only [sub_self, norm_zero]
    positivity
  · rw [sub_zero]
    exact ((ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord (selector_omega_le hu) f).val.norm_coe_le_norm _).trans
      (norm_ordinalSpaceEndpointZeroBoundedEquiv_le c.ord (selector_omega_le hu) f)

end Posets.UniverseRegularMatrix


