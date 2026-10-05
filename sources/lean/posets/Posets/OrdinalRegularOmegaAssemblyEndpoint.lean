import JLMS.OrdinalSpaceEndpointZero
import JLMS.PointDifferenceEvaluation

/-! Restriction identifies the actual endpoint-zero kernel isometrically
with C₀ of the half-open ordinal interval. The inverse really extends by
zero at the missing endpoint via the one-point compactification. -/
noncomputable section
open Set Filter Topology
open scoped OnePoint
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
local instance ordinalOmegaEndpointFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance ordinalOmegaEndpointFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance ordinalOmegaEndpointKernelGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance ordinalOmegaEndpointKernelSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance

def ordinalHalfOpenInclusion (α : Ordinal.{u}) : Iio α → JLMS.OrdinalInterval α :=
  fun x => ⟨x.val, Ordinal.zero_le _, x.property.le⟩

theorem ordinalHalfOpenInclusion_isEmbedding (α : Ordinal.{u}) :
    IsEmbedding (ordinalHalfOpenInclusion α) :=
  IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    (show IsEmbedding (Subtype.val ∘ ordinalHalfOpenInclusion α) from IsEmbedding.subtypeVal)

theorem ordinalHalfOpenInclusion_range (α : Ordinal.{u}) :
    range (ordinalHalfOpenInclusion α) =
      {(⟨α, Ordinal.zero_le _, le_rfl⟩ : JLMS.OrdinalInterval α)}ᶜ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ h
    exact y.property.ne (congrArg Subtype.val (mem_singleton_iff.mp h))
  · intro hx
    have hne : x.val ≠ α := by
      intro he
      apply hx
      exact mem_singleton_iff.mpr (Subtype.ext he)
    exact ⟨⟨x.val, lt_of_le_of_ne x.property.2 hne⟩, Subtype.ext rfl⟩

def ordinalHalfOpenOnePointHomeomorph (α : Ordinal.{u}) :
    OnePoint (Iio α) ≃ₜ JLMS.OrdinalInterval α :=
  OnePoint.equivOfIsEmbeddingOfRangeEq ⟨α, Ordinal.zero_le _, le_rfl⟩
    (ordinalHalfOpenInclusion α) (ordinalHalfOpenInclusion_isEmbedding α)
    (ordinalHalfOpenInclusion_range α)

@[simp] theorem ordinalHalfOpenOnePointHomeomorph_coe (α : Ordinal.{u}) (x : Iio α) :
    ordinalHalfOpenOnePointHomeomorph α x = ordinalHalfOpenInclusion α x := rfl

@[simp] theorem ordinalHalfOpenOnePointHomeomorph_infty (α : Ordinal.{u}) :
    ordinalHalfOpenOnePointHomeomorph α ∞ = ⟨α, Ordinal.zero_le _, le_rfl⟩ := rfl

def ordinalEndpointCZeroRestriction (α : Ordinal.{u}) (f : JLMS.ordinalEndpointZero 𝕜 α) :
    JLMS.CZero 𝕜 (Iio α) where
  toFun x := f.val (ordinalHalfOpenInclusion α x)
  continuous_toFun := f.val.continuous.comp (ordinalHalfOpenInclusion_isEmbedding α).continuous
  zero_at_infty' := by
    have hf : f.val ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0 := f.property
    have hcoe : Tendsto (fun x : Iio α => (x : OnePoint (Iio α))) (cocompact (Iio α)) (𝓝 ∞) := by
      simpa only [coclosedCompact_eq_cocompact] using
        (OnePoint.tendsto_coe_infty (X := Iio α))
    have ht := (f.val.continuous.comp (ordinalHalfOpenOnePointHomeomorph α).continuous).tendsto ∞
    simpa only [ordinalHalfOpenOnePointHomeomorph_coe, ordinalHalfOpenOnePointHomeomorph_infty,
      Function.comp_apply, hf] using ht.comp hcoe

@[simp] theorem ordinalEndpointCZeroRestriction_apply (α : Ordinal.{u})
    (f : JLMS.ordinalEndpointZero 𝕜 α) (x : Iio α) :
    ordinalEndpointCZeroRestriction α f x = f.val (ordinalHalfOpenInclusion α x) := rfl

theorem ordinalEndpointCZeroRestriction_norm (α : Ordinal.{u})
    (f : JLMS.ordinalEndpointZero 𝕜 α) : ‖ordinalEndpointCZeroRestriction α f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    exact fun x => f.val.norm_coe_le_norm (ordinalHalfOpenInclusion α x)
  · change ‖f.val‖ ≤ ‖ordinalEndpointCZeroRestriction α f‖
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    obtain hx | hx := lt_or_eq_of_le x.property.2
    · exact JLMS.norm_CZero_apply_le (ordinalEndpointCZeroRestriction α f) ⟨x.val, hx⟩
    · have he : x = (⟨α, Ordinal.zero_le _, le_rfl⟩ : JLMS.OrdinalInterval α) := Subtype.ext hx
      have hf : f.val ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0 := f.property
      rw [he, hf, norm_zero]
      exact norm_nonneg _

theorem ordinalEndpointCZeroRestriction_surjective (α : Ordinal.{u}) :
    Function.Surjective (ordinalEndpointCZeroRestriction (𝕜 := 𝕜) α) := by
  intro g
  let e := ordinalHalfOpenOnePointHomeomorph α
  let f : JLMS.OrdinalC 𝕜 α :=
    ⟨fun x => JLMS.extendCZeroOnePoint g (e.symm x),
      (JLMS.extendCZeroOnePoint g).continuous.comp e.symm.continuous⟩
  have hf : f ∈ JLMS.ordinalEndpointZero 𝕜 α := by
    change JLMS.extendCZeroOnePoint g (e.symm (e ∞)) = 0
    rw [e.symm_apply_apply]
    rfl
  refine ⟨⟨f, hf⟩, ?_⟩
  ext x
  change JLMS.extendCZeroOnePoint g (e.symm (e (x : OnePoint (Iio α)))) = g x
  rw [e.symm_apply_apply]
  rfl

def ordinalEndpointCZeroIsometry (α : Ordinal.{u}) :
    JLMS.ordinalEndpointZero 𝕜 α ≃ₗᵢ[𝕜] JLMS.CZero 𝕜 (Iio α) :=
  LinearIsometryEquiv.ofSurjective
    { toFun := ordinalEndpointCZeroRestriction α
      map_add' f g := by ext x; rfl
      map_smul' c f := by ext x; rfl
      norm_map' := ordinalEndpointCZeroRestriction_norm α }
    (ordinalEndpointCZeroRestriction_surjective α)

@[simp] theorem ordinalEndpointCZeroIsometry_apply (α : Ordinal.{u})
    (f : JLMS.ordinalEndpointZero 𝕜 α) (x : Iio α) :
    ordinalEndpointCZeroIsometry (𝕜 := 𝕜) α f x = f.val (ordinalHalfOpenInclusion α x) := rfl

end Posets

