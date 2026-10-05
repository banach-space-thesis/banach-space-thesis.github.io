import JLMS.OrdinalLimitProjection
import JLMS.OrdinalSpaceEndpointZero

/-!
# Splitting along a cofinal embedded ordinal interval

Given a continuous strictly increasing cofinal map [0, γ] → [0, β],
restriction onto its image has a bounded right inverse obtained by rounding
up to that image. The resulting decomposition is C[0, β] ≃ C[0, γ] × ker P.
It respects endpoint evaluation and hence also splits the endpoint-zero
spaces. This supplies the projection part of Kislyakov's decomposition (3.1).
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace

local instance ordinalRetractionIntervalFact (α : Ordinal.{u}) :
    Fact ((0 : Ordinal.{u}) ≤ α) := ⟨Ordinal.zero_le _⟩

def ordinalEmbeddingCeiling {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (x : OrdinalInterval β) :
    OrdinalInterval γ := sInf {y | x ≤ g y}

theorem ordinalEmbeddingCeiling_spec {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β))
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (x : OrdinalInterval β) : x ≤ g (ordinalEmbeddingCeiling g x) := by
  apply csInf_mem (s := {y | x ≤ g y})
  refine ⟨⟨γ, Ordinal.zero_le _, le_rfl⟩, ?_⟩
  change x ≤ g ⟨γ, Ordinal.zero_le _, le_rfl⟩
  rw [htop]
  exact x.property.2

theorem ordinalEmbeddingCeiling_le_iff {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : Monotone g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (x : OrdinalInterval β) (y : OrdinalInterval γ) :
    ordinalEmbeddingCeiling g x ≤ y ↔ x ≤ g y := by
  constructor
  · intro h
    exact (ordinalEmbeddingCeiling_spec g htop x).trans (hg h)
  · exact fun h => sInf_le h

theorem ordinalEmbeddingCeiling_monotone {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : Monotone g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    Monotone (ordinalEmbeddingCeiling g) := by
  intro x y hxy
  exact (ordinalEmbeddingCeiling_le_iff g hg htop _ _).mpr
    (hxy.trans (ordinalEmbeddingCeiling_spec g htop y))

theorem ordinalEmbeddingCeiling_apply_image {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (x : OrdinalInterval γ) : ordinalEmbeddingCeiling g (g x) = x := by
  apply le_antisymm
  · exact (ordinalEmbeddingCeiling_le_iff g hg.monotone htop _ _).mpr le_rfl
  · exact hg.le_iff_le.mp (ordinalEmbeddingCeiling_spec g htop (g x))

@[simp] theorem ordinalEmbeddingCeiling_endpoint {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    ordinalEmbeddingCeiling g ⟨β, Ordinal.zero_le _, le_rfl⟩ =
      ⟨γ, Ordinal.zero_le _, le_rfl⟩ := by
  rw [← htop]
  exact ordinalEmbeddingCeiling_apply_image g hg htop _

theorem ordinalEmbeddingCeiling_continuous {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : Monotone g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    Continuous (ordinalEmbeddingCeiling g) := by
  rw [OrderTopology.continuous_iff]
  intro b
  constructor
  · have he : ordinalEmbeddingCeiling g ⁻¹' Set.Ioi b = (ordinalHeadSet β (g b).val)ᶜ := by
      ext x
      change b < ordinalEmbeddingCeiling g x ↔ ¬ x.val ≤ (g b).val
      rw [lt_iff_not_ge, ordinalEmbeddingCeiling_le_iff g hg htop]
      rfl
    rw [he]
    exact (ordinalHeadSet_isClopen β (g b).val).isClosed.isOpen_compl
  · exact ((isLowerSet_Iio b).preimage (ordinalEmbeddingCeiling_monotone g hg htop)).isOpen

def ordinalEmbeddingCeilingMap {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    C(OrdinalInterval β, OrdinalInterval γ) :=
  ⟨ordinalEmbeddingCeiling g, ordinalEmbeddingCeiling_continuous g hg.monotone htop⟩

/-- Restriction to the embedded ordinal interval, in its original coordinates. -/
def ordinalSpaceRestriction {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) : OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 γ :=
  ({ toFun := fun f => f.comp g
     map_add' := fun f₁ f₂ => by ext x; rfl
     map_smul' := fun a f => by ext x; rfl } : OrdinalC 𝕜 β →ₗ[𝕜] OrdinalC 𝕜 γ).mkContinuous 1
    (fun f => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm (g x)))

@[simp] theorem ordinalSpaceRestriction_apply {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (f : OrdinalC 𝕜 β)
    (x : OrdinalInterval γ) : ordinalSpaceRestriction g f x = f (g x) := rfl

local instance ordinalRestrictionKernelGroup {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) :
    NormedAddCommGroup (LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) g)) := inferInstance
local instance ordinalRestrictionKernelSpace {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) :
    NormedSpace 𝕜 (LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) g)) := inferInstance

def ordinalSpaceCeilingExtension {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    OrdinalC 𝕜 γ →L[𝕜] OrdinalC 𝕜 β := ordinalSpaceRestriction (ordinalEmbeddingCeilingMap g hg htop)

@[simp] theorem ordinalSpaceCeilingExtension_apply {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 γ) (x : OrdinalInterval β) :
    ordinalSpaceCeilingExtension g hg htop f x = f (ordinalEmbeddingCeiling g x) := rfl

theorem ordinalSpaceRestriction_ceilingExtension {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 γ) :
    ordinalSpaceRestriction g (ordinalSpaceCeilingExtension g hg htop f) = f := by
  ext x
  simp [ordinalEmbeddingCeiling_apply_image g hg htop]

theorem ordinalSpaceRestriction_kernel_endpointZero {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β))
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) g) ≤ ordinalEndpointZero 𝕜 β := by
  intro f hf
  change ordinalSpaceRestriction g f = 0 at hf
  change f ⟨β, Ordinal.zero_le _, le_rfl⟩ = 0
  have he := congrArg (fun w : OrdinalC 𝕜 γ => w ⟨γ, Ordinal.zero_le _, le_rfl⟩) hf
  simpa only [ordinalSpaceRestriction_apply, htop, ContinuousMap.zero_apply] using he

/-- The projection decomposition before identifying the kernel with its block sum. -/
def ordinalSpaceRetractionEquiv {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    OrdinalC 𝕜 β ≃L[𝕜] OrdinalC 𝕜 γ × LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) g) :=
  ContinuousLinearEquiv.equivOfRightInverse (R := 𝕜)
    (M := OrdinalC 𝕜 β) (M₂ := OrdinalC 𝕜 γ) (ordinalSpaceRestriction g)
    (ordinalSpaceCeilingExtension g hg htop) (ordinalSpaceRestriction_ceilingExtension g hg htop)

@[simp] theorem ordinalSpaceRetractionEquiv_fst {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 β) : (ordinalSpaceRetractionEquiv g hg htop f).1 =
      ordinalSpaceRestriction g f := rfl

/-- Restrict a product decomposition when a functional depends only on its first factor. -/
def kernelEquivOfProductFunctional
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (χE : E →L[𝕜] 𝕜) (χF : F →L[𝕜] 𝕜) (e : E ≃L[𝕜] F × G)
    (he : ∀ x, χE x = χF (e x).1) : LinearMap.ker χE ≃L[𝕜] LinearMap.ker χF × G := by
  have hforward (x : LinearMap.ker χE) : (e x.val).1 ∈ LinearMap.ker χF := by
    change χF (e x.val).1 = 0
    rw [← he]
    exact x.property
  have hbackward (y : LinearMap.ker χF × G) : e.symm (y.1.val, y.2) ∈ LinearMap.ker χE := by
    change χE (e.symm (y.1.val, y.2)) = 0
    rw [he, e.apply_symm_apply]
    exact y.1.property
  exact
    { toFun := fun x => (⟨(e x.val).1, hforward x⟩, (e x.val).2)
      invFun := fun y => ⟨e.symm (y.1.val, y.2), hbackward y⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => by
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun p : F × G => p.1) (e.apply_symm_apply (y.1.val, y.2))
        · exact congrArg (fun p : F × G => p.2) (e.apply_symm_apply (y.1.val, y.2))
      map_add' := fun x y => by
        apply Prod.ext
        · exact Subtype.ext (congrArg (fun p : F × G => p.1) (e.map_add x.val y.val))
        · exact congrArg (fun p : F × G => p.2) (e.map_add x.val y.val)
      map_smul' := fun a x => by
        apply Prod.ext
        · exact Subtype.ext (congrArg (fun p : F × G => p.1) (e.map_smul a x.val))
        · exact congrArg (fun p : F × G => p.2) (e.map_smul a x.val)
      continuous_toFun :=
        ((e.continuous.comp continuous_subtype_val).fst.subtype_mk _).prodMk
          (e.continuous.comp continuous_subtype_val).snd
      continuous_invFun :=
        (e.symm.continuous.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _ }

/-- The endpoint-zero form of the ordinal projection decomposition. -/
def ordinalEndpointZeroRetractionEquiv {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    ordinalEndpointZero 𝕜 β ≃L[𝕜]
      ordinalEndpointZero 𝕜 γ × LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) g) := by
  apply kernelEquivOfProductFunctional (𝕜 := 𝕜)
    (E := OrdinalC 𝕜 β) (F := OrdinalC 𝕜 γ)
    (G := LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) g))
    (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) ⟨γ, Ordinal.zero_le _, le_rfl⟩)
    (ordinalSpaceRetractionEquiv g hg htop)
  intro f
  change f ⟨β, Ordinal.zero_le _, le_rfl⟩ = f (g ⟨γ, Ordinal.zero_le _, le_rfl⟩)
  rw [htop]

end JLMS
