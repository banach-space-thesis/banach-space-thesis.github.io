import JLMS.OrdinalProjectionCopiesRange
import Mathlib.Order.CompleteLatticeIntervals

/-!
# Projections obtained by rounding up to a cofinal copy

A strictly increasing continuous map of [0, α] into itself which fixes α
has a continuous ceiling inverse: the least index whose image is at least
the specified point. Pullback along this inverse gives a complemented copy
of C[0, α]. This is the mechanism underlying the limit-row projection V in
Ogden Proposition 6.16.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance ordinalLimitFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance ordinalLimitFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance ordinalLimitOperatorGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) := inferInstance
local instance ordinalLimitOperatorSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) := inferInstance
local instance ordinalLimitOperatorAlgebra (α : Ordinal.{u}) :
    NormedAlgebra 𝕜 (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) := ContinuousLinearMap.toNormedAlgebra
local instance ordinalLimitOperatorScalarTower (α : Ordinal.{u}) :
    IsScalarTower 𝕜 (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
      (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) where
  smul_assoc c S T := by ext f x; rfl
local instance ordinalLimitOperatorScalarComm (α : Ordinal.{u}) :
    SMulCommClass 𝕜 (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
      (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) where
  smul_comm c S T := by
    ext f x
    change c • S (T f) x = S (c • T f) x
    rw [map_smul]
    rfl

local instance limitProjectionIntervalFact (α : Ordinal.{u}) :
    Fact ((0 : Ordinal.{u}) ≤ α) := ⟨Ordinal.zero_le _⟩

def ordinalCeiling (α : Ordinal.{u}) (g : C(OrdinalInterval α, OrdinalInterval α))
    (x : OrdinalInterval α) : OrdinalInterval α := sInf {y | x ≤ g y}

theorem ordinalCeiling_spec (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α))
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩)
    (x : OrdinalInterval α) : x ≤ g (ordinalCeiling α g x) := by
  apply csInf_mem (s := {y | x ≤ g y})
  refine ⟨⟨α, Ordinal.zero_le _, le_rfl⟩, ?_⟩
  change x ≤ g ⟨α, Ordinal.zero_le _, le_rfl⟩
  rw [htop]
  exact x.property.2

theorem ordinalCeiling_le_iff (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩)
    (x y : OrdinalInterval α) : ordinalCeiling α g x ≤ y ↔ x ≤ g y := by
  constructor
  · intro h
    exact (ordinalCeiling_spec α g htop x).trans (hg h)
  · intro h
    exact sInf_le h

theorem ordinalCeiling_monotone (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    Monotone (ordinalCeiling α g) := by
  intro x y hxy
  apply (ordinalCeiling_le_iff α g hg htop _ _).mpr
  exact hxy.trans (ordinalCeiling_spec α g htop y)

theorem ordinalCeiling_apply_image (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : StrictMono g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩)
    (x : OrdinalInterval α) : ordinalCeiling α g (g x) = x := by
  apply le_antisymm
  · exact (ordinalCeiling_le_iff α g hg.monotone htop _ _).mpr le_rfl
  · exact hg.le_iff_le.mp (ordinalCeiling_spec α g htop (g x))

theorem ordinalCeiling_continuous (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    Continuous (ordinalCeiling α g) := by
  rw [OrderTopology.continuous_iff]
  intro b
  constructor
  · have he : ordinalCeiling α g ⁻¹' Set.Ioi b = (ordinalHeadSet α (g b).val)ᶜ := by
      ext x
      change b < ordinalCeiling α g x ↔ ¬ x.val ≤ (g b).val
      rw [lt_iff_not_ge, ordinalCeiling_le_iff α g hg htop]
      rfl
    rw [he]
    exact (ordinalHeadSet_isClopen α (g b).val).isClosed.isOpen_compl
  · exact ((isLowerSet_Iio b).preimage (ordinalCeiling_monotone α g hg htop)).isOpen

def ordinalCeilingMap (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    C(OrdinalInterval α, OrdinalInterval α) :=
  ⟨ordinalCeiling α g, ordinalCeiling_continuous α g hg htop⟩

/-- Pullback by the ceiling inverse embeds the whole continuous-function space. -/
def ordinalCeilingExtension (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α :=
  ordinalTailPrecompose α (ordinalCeilingMap α g hg htop)

/-- The projection replaces a function's value by its value at the next point
of the chosen cofinal copy. -/
def ordinalCeilingProjection (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α :=
  (ordinalCeilingExtension α g hg htop).comp (ordinalTailPrecompose α g)

@[simp] theorem ordinalCeilingExtension_apply (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 α) (x : OrdinalInterval α) :
    ordinalCeilingExtension α g hg htop f x = f (ordinalCeiling α g x) := rfl

@[simp] theorem ordinalCeilingProjection_apply (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 α) (x : OrdinalInterval α) :
    ordinalCeilingProjection α g hg htop f x = f (g (ordinalCeiling α g x)) := rfl

theorem ordinalCeilingRestriction_extension (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : StrictMono g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    (ordinalTailPrecompose (𝕜 := 𝕜) α g).comp (ordinalCeilingExtension α g hg.monotone htop) =
      ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α) := by
  ext f x
  simp [ordinalCeiling_apply_image α g hg htop]

theorem ordinalCeilingProjection_idempotent (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : StrictMono g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    (ordinalCeilingProjection (𝕜 := 𝕜) α g hg.monotone htop).comp
      (ordinalCeilingProjection α g hg.monotone htop) =
        ordinalCeilingProjection α g hg.monotone htop := by
  ext f x
  simp [ordinalCeiling_apply_image α g hg htop]

theorem ordinalCeilingProjectionComplement_mem_continuityIdeal
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    (α : Ordinal.{u}) (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : StrictMono g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩)
    (θ : (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →ₙₐ[𝕜] A) :
    1 - ordinalCeilingProjection (𝕜 := 𝕜) α g hg.monotone htop ∈
      continuityIdeal (𝕜 := 𝕜) (B := OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (A := A) θ := by
  exact complement_mem_continuityIdeal_of_retraction θ
    (ordinalCeilingExtension α g hg.monotone htop) (ordinalTailPrecompose α g)
    (ordinalCeilingRestriction_extension α g hg htop)

/-- An operator with zero values at the selected rows is killed by V. -/
theorem ordinalCeilingProjection_comp_eq_zero (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : Monotone g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hzero : ∀ (f : OrdinalC 𝕜 α) (x : OrdinalInterval α), T f (g x) = 0) :
    (ordinalCeilingProjection α g hg htop).comp T = 0 := by
  ext f x
  exact hzero f (ordinalCeiling α g x)

theorem mem_continuityIdeal_of_zero_cofinal_rows
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    (α : Ordinal.{u}) (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : StrictMono g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩)
    (θ : (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →ₙₐ[𝕜] A)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hzero : ∀ (f : OrdinalC 𝕜 α) (x : OrdinalInterval α), T f (g x) = 0) :
    T ∈ continuityIdeal (𝕜 := 𝕜) (B := OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (A := A) θ := by
  have hV : ordinalCeilingProjection α g hg.monotone htop * T = 0 :=
    ordinalCeilingProjection_comp_eq_zero α g hg.monotone htop T hzero
  have hm := continuityIdeal_mul_right θ T
    (ordinalCeilingProjectionComplement_mem_continuityIdeal α g hg htop θ)
  simpa only [sub_mul, one_mul, hV, sub_zero] using hm

def ordinalCeilingProjectionRangeEquiv (α : Ordinal.{u})
    (g : C(OrdinalInterval α, OrdinalInterval α)) (hg : StrictMono g)
    (htop : g ⟨α, Ordinal.zero_le _, le_rfl⟩ = ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    OrdinalC 𝕜 α ≃L[𝕜]
      LinearMap.range (ordinalCeilingProjection (𝕜 := 𝕜) α g hg.monotone htop) :=
  projectionRangeEquivOfRetraction (ordinalCeilingExtension α g hg.monotone htop)
    (ordinalTailPrecompose α g) (ordinalCeilingProjection α g hg.monotone htop)
    (ordinalCeilingRestriction_extension α g hg htop) rfl

end JLMS
