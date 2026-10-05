import JLMS.OrdinalSpaceEndpointZero
import JLMS.OrdinalTailConstancy
import ThesisCommon.Analysis.ContinuousMapPullback

/-! Actual initial-segment retractions between endpoint-zero ordinal spaces.
Extension is isometric; restriction followed by subtraction of the new endpoint
has norm at most two. The bounds are independent of both ordinals. -/

noncomputable section
namespace Posets
open JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

local instance endpointRetractionFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance endpointRetractionFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance endpointRetractionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance endpointRetractionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

def ordinalEndpointExtend (α β : Ordinal.{u}) (h : α ≤ β) :
    ordinalEndpointZero 𝕜 α →L[𝕜] ordinalEndpointZero 𝕜 β := by
  let F : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 β :=
    ThesisCommon.continuousMapPullback
      ((ordinalIntervalClamp α).comp ⟨Subtype.val, continuous_subtype_val⟩)
  exact (F.comp (ordinalEndpointZero 𝕜 α).subtypeL).codRestrict
    (ordinalEndpointZero 𝕜 β) (fun x => by
      change x.val ⟨min β α, _⟩ = 0
      have he : (⟨min β α, Ordinal.zero_le _, min_le_right _ _⟩ : OrdinalInterval α) =
          ⟨α, Ordinal.zero_le _, le_rfl⟩ := Subtype.ext (min_eq_right h)
      rw [he]
      exact x.property)

@[simp] theorem ordinalEndpointExtend_apply (α β : Ordinal.{u}) (h : α ≤ β)
    (x : ordinalEndpointZero 𝕜 α) (t : OrdinalInterval β) :
    (ordinalEndpointExtend (𝕜 := 𝕜) α β h x).val t =
      x.val (ordinalIntervalClamp α t.val) := rfl

def ordinalEndpointRead (α β : Ordinal.{u}) (h : α ≤ β) :
    ordinalEndpointZero 𝕜 β →L[𝕜] ordinalEndpointZero 𝕜 α := by
  let R : OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 α :=
    ThesisCommon.continuousMapPullback
      ⟨fun x => ⟨x.val, x.property.1, x.property.2.trans h⟩,
        continuous_subtype_val.subtype_mk _⟩
  let φ : OrdinalC 𝕜 β →L[𝕜] 𝕜 :=
    ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) ⟨α, Ordinal.zero_le _, h⟩
  let F := R - φ.smulRight (ContinuousMap.const (OrdinalInterval α) (1 : 𝕜))
  exact (F.comp (ordinalEndpointZero 𝕜 β).subtypeL).codRestrict
    (ordinalEndpointZero 𝕜 α) (fun x => by
      change x.val ⟨α, Ordinal.zero_le _, h⟩ -
        x.val ⟨α, Ordinal.zero_le _, h⟩ • (1 : 𝕜) = 0
      simp)

@[simp] theorem ordinalEndpointRead_apply (α β : Ordinal.{u}) (h : α ≤ β)
    (x : ordinalEndpointZero 𝕜 β) (t : OrdinalInterval α) :
    (ordinalEndpointRead (𝕜 := 𝕜) α β h x).val t =
      x.val ⟨t.val, t.property.1, t.property.2.trans h⟩ -
        x.val ⟨α, Ordinal.zero_le _, h⟩ := by
  change x.val ⟨t.val, t.property.1, t.property.2.trans h⟩ -
    x.val ⟨α, Ordinal.zero_le _, h⟩ • (1 : 𝕜) = _
  simp only [smul_eq_mul, mul_one]

@[simp] theorem ordinalEndpointRead_extend (α β : Ordinal.{u}) (h : α ≤ β)
    (x : ordinalEndpointZero 𝕜 α) :
    ordinalEndpointRead (𝕜 := 𝕜) α β h (ordinalEndpointExtend α β h x) = x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [ordinalEndpointRead_apply, ordinalEndpointExtend_apply, ordinalEndpointExtend_apply]
  have hx : x.val ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0 := x.property
  have he : ordinalIntervalClamp α α = ⟨α, Ordinal.zero_le _, le_rfl⟩ :=
    Subtype.ext (min_self α)
  change x.val (ordinalIntervalClamp α t.val) - x.val (ordinalIntervalClamp α α) = x.val t
  rw [ordinalIntervalClamp_coe, he, hx, sub_zero]

theorem norm_ordinalEndpointExtend_le (α β : Ordinal.{u}) (h : α ≤ β) :
    ‖ordinalEndpointExtend (𝕜 := 𝕜) α β h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  change ‖(ordinalEndpointExtend (𝕜 := 𝕜) α β h x).val‖ ≤ ‖x.val‖
  apply (ContinuousMap.norm_le _ (norm_nonneg x.val)).mpr
  intro t
  rw [ordinalEndpointExtend_apply]
  exact x.val.norm_coe_le_norm _

theorem norm_ordinalEndpointRead_le (α β : Ordinal.{u}) (h : α ≤ β) :
    ‖ordinalEndpointRead (𝕜 := 𝕜) α β h‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(ordinalEndpointRead (𝕜 := 𝕜) α β h x).val‖ ≤ 2 * ‖x.val‖
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg x.val))).mpr
  intro t
  rw [ordinalEndpointRead_apply]
  exact (norm_sub_le _ _).trans (by
    nlinarith [x.val.norm_coe_le_norm ⟨t.val, t.property.1, t.property.2.trans h⟩,
      x.val.norm_coe_le_norm ⟨α, Ordinal.zero_le _, h⟩])

theorem norm_ordinalEndpointExtend (α β : Ordinal.{u}) (h : α ≤ β)
    (x : ordinalEndpointZero 𝕜 α) :
    ‖ordinalEndpointExtend (𝕜 := 𝕜) α β h x‖ = ‖x‖ := by
  apply le_antisymm
  · calc
      _ ≤ ‖ordinalEndpointExtend (𝕜 := 𝕜) α β h‖ * ‖x‖ :=
        (ordinalEndpointExtend (𝕜 := 𝕜) α β h).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (norm_ordinalEndpointExtend_le (𝕜 := 𝕜) α β h) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  · change ‖x.val‖ ≤ ‖(ordinalEndpointExtend (𝕜 := 𝕜) α β h x).val‖
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    have ht := (ordinalEndpointExtend (𝕜 := 𝕜) α β h x).val.norm_coe_le_norm
      ⟨t.val, t.property.1, t.property.2.trans h⟩
    simpa only [ordinalEndpointExtend_apply, ordinalIntervalClamp_coe] using ht

end Posets
