import JLMS.OrdinalSpaceBlocksRestriction
import JLMS.OrdinalSpaceRetraction
import JLMS.ClopenFunctionExtension
import JLMS.CZeroSumSynthesis

/-!
# Coordinates of the kernel of ordinal restriction

Functions vanishing on the entire embedded interval restrict to endpoint-zero
functions on each block. The compactness estimate makes those coordinates
a dependent c₀ family, and their supremum norm is exactly the original norm.
-/

noncomputable section
namespace JLMS
open Filter Topology
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}

attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace

theorem ordinalSpaceRestriction_kernel_zero
    (L : C(OrdinalInterval γ, OrdinalInterval β))
    (f : LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) L))
    (x : OrdinalInterval γ) : f.val (L x) = 0 :=
  congrArg (fun g : OrdinalC 𝕜 γ => g x) f.prop

def ordinalSpaceBlockKernelCoordinate
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (ξ : Set.Iio γ) (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (f : LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) L)) :
    ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ) :=
  ⟨continuousMapDomainIsometry (𝕜 := 𝕜) (ordinalSpaceBlockHomeomorph L hL ξ hξ)
    (f.val.restrict (ordinalSpaceBlockSet L ξ)), by
      change f.val (ordinalSpaceBlockHomeomorph L hL ξ hξ
        ⟨ordinalSpaceBlockLength L ξ, Ordinal.zero_le _, le_rfl⟩).val = 0
      rw [ordinalSpaceBlockHomeomorph_endpoint]
      exact ordinalSpaceRestriction_kernel_zero L f _⟩

theorem norm_ordinalSpaceBlockKernelCoordinate
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (ξ : Set.Iio γ) (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (f : LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) L)) :
    ‖ordinalSpaceBlockKernelCoordinate L hL ξ hξ f‖ =
      ‖f.val.restrict (ordinalSpaceBlockSet L ξ)‖ :=
  (continuousMapDomainIsometry (𝕜 := 𝕜) (ordinalSpaceBlockHomeomorph L hL ξ hξ)).norm_map _

def ordinalSpaceKernelCoordinates
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (f : LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) L)) :
    CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)) :=
  CZeroSum.mk (fun ξ => ordinalSpaceBlockKernelCoordinate L hL ξ (hblocks ξ) f) (by
    simpa only [norm_ordinalSpaceBlockKernelCoordinate] using
      tendsto_norm_ordinalSpaceBlockRestrictions L hL hzero htop f.val
        (ordinalSpaceRestriction_kernel_zero L f))

theorem norm_ordinalSpaceKernelCoordinates
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (f : LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) L)) :
    ‖ordinalSpaceKernelCoordinates L hL hzero htop hblocks f‖ = ‖f‖ := by
  let v := ordinalSpaceKernelCoordinates L hL hzero htop hblocks f
  apply le_antisymm
  · apply CZeroSum.norm_le (norm_nonneg f)
    intro ξ
    change ‖ordinalSpaceBlockKernelCoordinate L hL ξ (hblocks ξ) f‖ ≤ ‖f‖
    rw [norm_ordinalSpaceBlockKernelCoordinate]
    exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      (fun x => f.val.norm_coe_le_norm x.val)
  · change ‖f.val‖ ≤ ‖v‖
    apply (ContinuousMap.norm_le _ (norm_nonneg v)).mpr
    intro x
    by_cases hx : x ∈ Set.range L
    · obtain ⟨y, rfl⟩ := hx
      rw [ordinalSpaceRestriction_kernel_zero L f y, norm_zero]
      exact norm_nonneg v
    · obtain ⟨ξ, hξ⟩ := exists_ordinalSpaceBlock_of_not_mem_range L hL hzero htop x hx
      calc
        ‖f.val x‖ ≤ ‖f.val.restrict (ordinalSpaceBlockSet L ξ)‖ :=
          (f.val.restrict (ordinalSpaceBlockSet L ξ)).norm_coe_le_norm ⟨x, hξ⟩
        _ = ‖v ξ‖ := (norm_ordinalSpaceBlockKernelCoordinate L hL ξ (hblocks ξ) f).symm
        _ ≤ ‖v‖ := v.norm_apply_le_norm ξ

def ordinalSpaceKernelCoordinatesIsometry
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) L) →ₗᵢ[𝕜]
      CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)) where
  toFun := ordinalSpaceKernelCoordinates L hL hzero htop hblocks
  map_add' f g := by
    apply CZeroSum.ext
    intro ξ
    apply Subtype.ext
    ext z
    rfl
  map_smul' c f := by
    apply CZeroSum.ext
    intro ξ
    apply Subtype.ext
    ext z
    rfl
  norm_map' := norm_ordinalSpaceKernelCoordinates L hL hzero htop hblocks

def ordinalSpaceBlockExtension
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (ξ : Set.Iio γ) (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ) →L[𝕜] OrdinalC 𝕜 β :=
  (clopenFunctionExtension (𝕜 := 𝕜) (ordinalSpaceBlock_isClopen L ξ)).toContinuousLinearMap.comp
    ((continuousMapDomainIsometry (𝕜 := 𝕜) (ordinalSpaceBlockHomeomorph L hL ξ hξ)).symm.toLinearIsometry.toContinuousLinearMap.comp
        (ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)).subtypeL)

theorem ordinalSpaceBlockExtension_apply_point
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (ξ : Set.Iio γ) (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (f : ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ))
    (z : OrdinalInterval (ordinalSpaceBlockLength L ξ)) :
    ordinalSpaceBlockExtension L hL ξ hξ f (ordinalSpaceBlockHomeomorph L hL ξ hξ z).val =
      f.val z := by
  change clopenExtendFunction (ordinalSpaceBlock_isClopen L ξ)
    ((continuousMapDomainIsometry (𝕜 := 𝕜) (ordinalSpaceBlockHomeomorph L hL ξ hξ)).symm f.val)
      (ordinalSpaceBlockHomeomorph L hL ξ hξ z).val = _
  rw [clopenExtendFunction_of_mem _ _ _ (ordinalSpaceBlockHomeomorph L hL ξ hξ z).prop]
  change f.val ((ordinalSpaceBlockHomeomorph L hL ξ hξ).symm
    (ordinalSpaceBlockHomeomorph L hL ξ hξ z)) = _
  rw [Homeomorph.symm_apply_apply]

theorem ordinalSpaceBlockExtension_apply_of_not_mem
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (ξ : Set.Iio γ) (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (f : ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ))
    (x : OrdinalInterval β) (hx : x ∉ ordinalSpaceBlockSet L ξ) :
    ordinalSpaceBlockExtension L hL ξ hξ f x = 0 :=
  clopenExtendFunction_of_not_mem (ordinalSpaceBlock_isClopen L ξ) _ _ hx

theorem ordinalSpaceBlockExtension_range_zero
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (ξ : Set.Iio γ) (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (f : ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)) (η : OrdinalInterval γ) :
    ordinalSpaceBlockExtension L hL ξ hξ f (L η) = 0 := by
  classical
  by_cases hη : L η ∈ ordinalSpaceBlockSet L ξ
  · have hηeq := (ordinalSpaceBlock_range_mem_iff L hL ξ η).mp hη
    have he : L η = (ordinalSpaceBlockHomeomorph L hL ξ hξ
        ⟨ordinalSpaceBlockLength L ξ, Ordinal.zero_le _, le_rfl⟩).val := by
      rw [ordinalSpaceBlockHomeomorph_endpoint]
      exact congrArg L (Subtype.ext hηeq)
    rw [he, ordinalSpaceBlockExtension_apply_point]
    exact f.prop
  · exact ordinalSpaceBlockExtension_apply_of_not_mem L hL ξ hξ f (L η) hη

theorem norm_sum_ordinalSpaceBlockExtensions_le
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (x : ∀ ξ : Set.Iio γ, ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ))
    (s : Finset (Set.Iio γ)) (M : ℝ) (hM : 0 ≤ M) (hx : ∀ ξ ∈ s, ‖x ξ‖ ≤ M) :
    ‖∑ ξ ∈ s, ordinalSpaceBlockExtension L hL ξ (hblocks ξ) (x ξ)‖ ≤ M := by
  apply norm_sum_clopenFunctionExtensions_le (ordinalSpaceBlockSet L)
    (ordinalSpaceBlock_isClopen L) (ordinalSpaceBlocks_pairwiseDisjoint L hL)
      (fun ξ => (continuousMapDomainIsometry (𝕜 := 𝕜)
        (ordinalSpaceBlockHomeomorph L hL ξ (hblocks ξ))).symm (x ξ).val) s hM
  intro ξ hξ
  simpa only [LinearIsometryEquiv.norm_map] using hx ξ hξ

end JLMS
