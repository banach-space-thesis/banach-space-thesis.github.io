import JLMS.OrdinalTailConstancy
import JLMS.CZeroTools
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Ogden Proposition 6.16: the head projection J(β)

J(β) keeps a function's values on [0,β] and is zero on (β,α]. The cutoff
set is clopen in [0,α], so this is an actual bounded operator on the continuous
function space. Both it and its complementary projection have norm at most
one. This file uses the diagonal matrix definition on page 356 of Ogden.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalHeadSet (α β : Ordinal.{u}) : Set (OrdinalInterval α) := {x | x.val ≤ β}

theorem ordinalHeadSet_isClopen (α β : Ordinal.{u}) : IsClopen (ordinalHeadSet α β) := by
  constructor
  · exact isClosed_le continuous_subtype_val continuous_const
  · have h := (isOpen_Iio : IsOpen (Set.Iio (Order.succ β))).preimage
      (continuous_subtype_val : Continuous (Subtype.val : OrdinalInterval α → Ordinal.{u}))
    convert h using 1
    ext x
    change x.val ≤ β ↔ x.val < Order.succ β
    exact Order.lt_succ_iff.symm

def ordinalHeadIndicator (α β : Ordinal.{u}) : OrdinalC 𝕜 α :=
  (clopenIndicator (𝕜 := 𝕜) (ordinalHeadSet α β) (ordinalHeadSet_isClopen α β)
    (ordinalHeadSet_isClopen α β).isClosed.isCompact).toContinuousMap

@[simp] theorem ordinalHeadIndicator_apply (α β : Ordinal.{u}) (x : OrdinalInterval α) :
    ordinalHeadIndicator (𝕜 := 𝕜) α β x = if x.val ≤ β then 1 else 0 := by
  exact clopenIndicator_apply _ _ _ x

def ordinalHeadProjection (α β : Ordinal.{u}) : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α :=
  ContinuousLinearMap.mul 𝕜 (OrdinalC 𝕜 α) (ordinalHeadIndicator α β)

@[simp] theorem ordinalHeadProjection_apply (α β : Ordinal.{u}) (f : OrdinalC 𝕜 α)
    (x : OrdinalInterval α) :
    ordinalHeadProjection α β f x = if x.val ≤ β then f x else 0 := by
  change ordinalHeadIndicator (𝕜 := 𝕜) α β x * f x = _
  rw [ordinalHeadIndicator_apply]
  split_ifs <;> simp

theorem ordinalHeadProjection_idempotent (α β : Ordinal.{u}) :
    (ordinalHeadProjection (𝕜 := 𝕜) α β).comp (ordinalHeadProjection α β) =
      ordinalHeadProjection α β := by
  ext f x
  by_cases hx : x.val ≤ β <;> simp [hx]

theorem norm_ordinalHeadProjection_le (α β : Ordinal.{u}) :
    ‖ordinalHeadProjection (𝕜 := 𝕜) α β‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  by_cases hx : x.val ≤ β
  · simpa [hx] using f.norm_coe_le_norm x
  · simp [hx]

theorem norm_ordinalTailProjection_le (α β : Ordinal.{u}) :
    ‖(ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α)) - ordinalHeadProjection α β‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  change ‖f x - ordinalHeadProjection α β f x‖ ≤ ‖f‖
  by_cases hx : x.val ≤ β
  · simp [hx]
  · simpa [hx] using f.norm_coe_le_norm x

theorem norm_ordinalHeadProjection (α β : Ordinal.{u}) :
    ‖ordinalHeadProjection (𝕜 := 𝕜) α β‖ = 1 := by
  let J : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α := ordinalHeadProjection α β
  change ‖J‖ = 1
  apply le_antisymm (norm_ordinalHeadProjection_le α β)
  let f : OrdinalC 𝕜 α := ContinuousMap.const _ 1
  let x : OrdinalInterval α := ⟨0, le_rfl, Ordinal.zero_le _⟩
  have hf : ‖f‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro y
    simp [f]
  calc
    1 = ‖J f x‖ := by simp [J, x, f]
    _ ≤ ‖J f‖ := (J f).norm_coe_le_norm x
    _ ≤ ‖J‖ * ‖f‖ := J.le_opNorm f
    _ ≤ ‖J‖ * 1 := mul_le_mul_of_nonneg_left hf (norm_nonneg J)
    _ = ‖J‖ := mul_one _

theorem norm_ordinalTailProjection {α β : Ordinal.{u}} (hβα : β < α) :
    ‖(ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α)) - ordinalHeadProjection α β‖ = 1 := by
  let R := (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α)) - ordinalHeadProjection α β
  apply le_antisymm (norm_ordinalTailProjection_le α β)
  let f : OrdinalC 𝕜 α := ContinuousMap.const _ 1
  let x : OrdinalInterval α := ⟨α, Ordinal.zero_le _, le_rfl⟩
  have hf : ‖f‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro y
    simp [f]
  calc
    1 = ‖R f x‖ := by
      change 1 = ‖f x - ordinalHeadProjection α β f x‖
      simp [x, f, not_le_of_gt hβα]
    _ ≤ ‖R f‖ := (R f).norm_coe_le_norm x
    _ ≤ ‖R‖ * ‖f‖ := R.le_opNorm f
    _ ≤ ‖R‖ * 1 := mul_le_mul_of_nonneg_left hf (norm_nonneg R)
    _ = ‖R‖ := mul_one _

theorem ordinalHeadProjection_fixes_supported (α β : Ordinal.{u})
    (f : OrdinalC 𝕜 α) (hf : ∀ x : OrdinalInterval α, β < x.val → f x = 0) :
    ordinalHeadProjection α β f = f := by
  ext x
  by_cases hx : x.val ≤ β
  · simp [hx]
  · simp [hx, hf x (lt_of_not_ge hx)]

theorem exists_ordinalHeadProjection_fixes_zeroEndpoint {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (f : OrdinalC 𝕜 α)
    (hf : f ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0) :
    ∃ β < α, ordinalHeadProjection α β f = f := by
  obtain ⟨β, hβ, htail⟩ := exists_constant_ordinalC_tail hα f
  exact ⟨β, hβ, ordinalHeadProjection_fixes_supported α β f
    (fun x hx => (htail x hx).trans hf)⟩

end JLMS
