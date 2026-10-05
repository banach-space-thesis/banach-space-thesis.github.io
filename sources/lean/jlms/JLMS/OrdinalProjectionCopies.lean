import JLMS.OrdinalHeadProjection
import JLMS.OperatorProjectionIdeal
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# Complemented copies beyond an ordinal cutoff

The tail beyond β is a copy of [0, α] whenever (β + 1) + α = α.
The two bounded operators below implement extension by zero on this tail and
restriction to it. Their products give the identity and the complementary
head projection. This supplies the head-projection step in Ogden 6.16.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance ordinalProjectionFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance ordinalProjectionFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance ordinalProjectionOperatorGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) := inferInstance
local instance ordinalProjectionOperatorSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) := inferInstance
local instance ordinalProjectionOperatorAlgebra (α : Ordinal.{u}) :
    NormedAlgebra 𝕜 (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) := ContinuousLinearMap.toNormedAlgebra
local instance ordinalProjectionOperatorScalarTower (α : Ordinal.{u}) :
    IsScalarTower 𝕜 (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
      (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) where
  smul_assoc c S T := by ext f x; rfl
local instance ordinalProjectionOperatorScalarComm (α : Ordinal.{u}) :
    SMulCommClass 𝕜 (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
      (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) where
  smul_comm c S T := by
    ext f x
    change c • S (T f) x = S (c • T f) x
    rw [map_smul]
    rfl

/-- Ordinal subtraction is continuous in its first argument. -/
theorem continuous_ordinal_sub_right (δ : Ordinal.{u}) :
    Continuous (fun x : Ordinal.{u} => x - δ) := by
  rw [OrderTopology.continuous_iff]
  intro b
  constructor
  · convert (isOpen_Ioi : IsOpen (Set.Ioi (δ + b))) using 1
    ext x
    exact Ordinal.lt_sub
  · have hm : Monotone (fun x : Ordinal.{u} => x - δ) := by
      intro x y hxy
      exact Ordinal.sub_le.mpr (hxy.trans (Ordinal.le_add_sub y δ))
    exact ((isLowerSet_Iio b).preimage hm).isOpen

def ordinalTailSubtract (α β : Ordinal.{u}) :
    C(OrdinalInterval α, OrdinalInterval α) where
  toFun x := ⟨x.val - Order.succ β,
    Ordinal.zero_le _, (Ordinal.sub_le_self _ _).trans x.property.2⟩
  continuous_toFun :=
    ((continuous_ordinal_sub_right (Order.succ β)).comp continuous_subtype_val).subtype_mk _

def ordinalTailShift (α β : Ordinal.{u}) (h : Order.succ β + α = α) :
    C(OrdinalInterval α, OrdinalInterval α) where
  toFun x := ⟨Order.succ β + x.val, Ordinal.zero_le _,
    by simpa only [h] using add_le_add_left x.property.2 (Order.succ β)⟩
  continuous_toFun :=
    ((Ordinal.isNormal_add_right (Order.succ β)).continuous.comp
      continuous_subtype_val).subtype_mk _

theorem ordinalTailShift_strictMono (α β : Ordinal.{u})
    (h : Order.succ β + α = α) : StrictMono (ordinalTailShift α β h) := by
  intro x y hxy
  exact (Ordinal.isNormal_add_right (Order.succ β)).strictMono hxy

@[simp] theorem ordinalTailShift_endpoint (α β : Ordinal.{u})
    (h : Order.succ β + α = α) :
    ordinalTailShift α β h ⟨α, Ordinal.zero_le _, le_rfl⟩ =
      ⟨α, Ordinal.zero_le _, le_rfl⟩ := Subtype.ext h

theorem ordinalTailShift_above (α β : Ordinal.{u})
    (h : Order.succ β + α = α) (x : OrdinalInterval α) :
    β < (ordinalTailShift α β h x).val :=
  (Order.lt_succ β).trans_le (Ordinal.le_add_right _ _)

/-- Precomposition, bundled with its sup-norm bound. -/
def ordinalTailPrecompose (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α :=
  ({ toFun := fun f => f.comp g
     map_add' := fun f₁ f₂ => by ext x; rfl
     map_smul' := fun a f => by ext x; rfl } : OrdinalC 𝕜 α →ₗ[𝕜] OrdinalC 𝕜 α).mkContinuous 1
    (fun f => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm (g x)))

@[simp] theorem ordinalTailPrecompose_apply (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (f : OrdinalC 𝕜 α)
    (x : OrdinalInterval α) : ordinalTailPrecompose α g f x = f (g x) := rfl

def ordinalTailExtension (α β : Ordinal.{u}) : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α :=
  (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α) - ordinalHeadProjection α β).comp
    (ordinalTailPrecompose α (ordinalTailSubtract α β))

def ordinalTailRestriction (α β : Ordinal.{u}) (h : Order.succ β + α = α) :
    OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α := ordinalTailPrecompose α (ordinalTailShift α β h)

@[simp] theorem ordinalTailExtension_apply (α β : Ordinal.{u}) (f : OrdinalC 𝕜 α)
    (x : OrdinalInterval α) :
    ordinalTailExtension α β f x = if x.val ≤ β then 0 else f (ordinalTailSubtract α β x) := by
  change f (ordinalTailSubtract α β x) -
    ordinalHeadProjection α β (ordinalTailPrecompose α (ordinalTailSubtract α β) f) x = _
  by_cases hx : x.val ≤ β <;> simp [hx]

@[simp] theorem ordinalTailRestriction_apply (α β : Ordinal.{u})
    (h : Order.succ β + α = α) (f : OrdinalC 𝕜 α) (x : OrdinalInterval α) :
    ordinalTailRestriction α β h f x = f (ordinalTailShift α β h x) := rfl

theorem ordinalTailRestriction_extension (α β : Ordinal.{u})
    (h : Order.succ β + α = α) :
    (ordinalTailRestriction (𝕜 := 𝕜) α β h).comp (ordinalTailExtension α β) =
      ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α) := by
  ext f x
  have hx : ¬ (ordinalTailShift α β h x).val ≤ β := by
    exact not_le_of_gt ((Order.lt_succ β).trans_le (Ordinal.le_add_right _ _))
  have he : ordinalTailSubtract α β (ordinalTailShift α β h x) = x := by
    apply Subtype.ext
    exact Ordinal.add_sub_cancel _ _
  simp [hx, he]

theorem ordinalTailExtension_restriction (α β : Ordinal.{u})
    (h : Order.succ β + α = α) :
    (ordinalTailExtension (𝕜 := 𝕜) α β).comp (ordinalTailRestriction α β h) =
      ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α) - ordinalHeadProjection α β := by
  ext f x
  change ordinalTailExtension α β (ordinalTailRestriction α β h f) x =
    f x - ordinalHeadProjection α β f x
  by_cases hx : x.val ≤ β
  · simp [hx]
  · have he : ordinalTailShift α β h (ordinalTailSubtract α β x) = x := by
      apply Subtype.ext
      exact Ordinal.add_sub_cancel_of_le (Order.succ_le_of_lt (lt_of_not_ge hx))
    simp [hx, he]

/-- The cutoff projection belongs to every homomorphism's continuity ideal. -/
theorem ordinalHeadProjection_mem_continuityIdeal_of_add
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    (α β : Ordinal.{u}) (h : Order.succ β + α = α)
    (θ : (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →ₙₐ[𝕜] A) :
    ordinalHeadProjection (𝕜 := 𝕜) α β ∈ continuityIdeal (𝕜 := 𝕜)
      (B := OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (A := A) θ := by
  have hvu : ordinalTailRestriction (𝕜 := 𝕜) α β h * ordinalTailExtension α β = 1 :=
    ordinalTailRestriction_extension α β h
  have huv : ordinalTailExtension (𝕜 := 𝕜) α β * ordinalTailRestriction α β h =
      1 - ordinalHeadProjection α β := ordinalTailExtension_restriction α β h
  simpa only [huv, sub_sub_cancel] using
    complement_mem_continuityIdeal_of_retraction θ (ordinalTailExtension α β)
      (ordinalTailRestriction α β h) hvu

/-- Infinite initial ordinals absorb any smaller ordinal on their left. -/
theorem initialOrdinal_succ_add {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c)
    {β : Ordinal.{u}} (hβ : β < c.ord) : Order.succ β + c.ord = c.ord := by
  apply (Ordinal.principal_add_iff_add_left_eq_self.mp (Ordinal.principal_add_ord hc))
  exact (Cardinal.isSuccLimit_ord hc).succ_lt hβ

theorem initialOrdinalHeadProjection_mem_continuityIdeal
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c) {β : Ordinal.{u}} (hβ : β < c.ord)
    (θ : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₙₐ[𝕜] A) :
    ordinalHeadProjection (𝕜 := 𝕜) c.ord β ∈ continuityIdeal (𝕜 := 𝕜)
      (B := OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (A := A) θ :=
  ordinalHeadProjection_mem_continuityIdeal_of_add c.ord β (initialOrdinal_succ_add hc hβ) θ

end JLMS
