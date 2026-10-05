import JLMS.OrdinalSpaceBlocksKernel

/-!
# Kislyakov's kernel as a dependent Banach c₀ sum

The inverse map sums the disjoint extensions by zero of the block functions.
Its finite sums satisfy the supremum estimate, so the series converges in
C[0,β]. Every summand vanishes on the embedded interval, and restriction of
the sum to a block returns exactly its prescribed coordinate. Thus the
previous isometric coordinate map is onto.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}
attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace
  ordinalRestrictionKernelGroup ordinalRestrictionKernelSpace

def ordinalSpaceBlocksSynthesis
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ))
      →L[𝕜] OrdinalC 𝕜 β :=
  cZeroSumSynthesis (fun ξ => ordinalSpaceBlockExtension (𝕜 := 𝕜) L hL ξ (hblocks ξ))
    (norm_sum_ordinalSpaceBlockExtensions_le (𝕜 := 𝕜) L hL hblocks)

theorem ordinalSpaceBlocksSynthesis_range_zero
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (x : CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)))
    (η : OrdinalInterval γ) : ordinalSpaceBlocksSynthesis (𝕜 := 𝕜) L hL hblocks x (L η) = 0 := by
  let ev := ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) (L η)
  have hs := (hasSum_cZeroSumSynthesis
    (fun ξ => ordinalSpaceBlockExtension (𝕜 := 𝕜) L hL ξ (hblocks ξ))
    (norm_sum_ordinalSpaceBlockExtensions_le (𝕜 := 𝕜) L hL hblocks) x).map ev ev.continuous
  change HasSum (fun ξ => ordinalSpaceBlockExtension (𝕜 := 𝕜) L hL ξ (hblocks ξ) (x ξ) (L η))
    (ordinalSpaceBlocksSynthesis (𝕜 := 𝕜) L hL hblocks x (L η)) at hs
  simp only [ordinalSpaceBlockExtension_range_zero] at hs
  exact hs.unique hasSum_zero

def ordinalSpaceBlocksKernelSynthesis
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ))
      →L[𝕜] LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) L) :=
  (ordinalSpaceBlocksSynthesis (𝕜 := 𝕜) L hL hblocks).codRestrict _ (fun x => by
    change ordinalSpaceRestriction L (ordinalSpaceBlocksSynthesis (𝕜 := 𝕜) L hL hblocks x) = 0
    ext η
    exact ordinalSpaceBlocksSynthesis_range_zero L hL hblocks x η)

theorem ordinalSpaceBlocksSynthesis_apply_point
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (x : CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)))
    (ξ : Set.Iio γ) (z : OrdinalInterval (ordinalSpaceBlockLength L ξ)) :
    ordinalSpaceBlocksSynthesis (𝕜 := 𝕜) L hL hblocks x
      (ordinalSpaceBlockHomeomorph L hL ξ (hblocks ξ) z).val = (x ξ).val z := by
  classical
  let p := ordinalSpaceBlockHomeomorph L hL ξ (hblocks ξ) z
  let ev := ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) p.val
  have hs := (hasSum_cZeroSumSynthesis
    (fun η => ordinalSpaceBlockExtension (𝕜 := 𝕜) L hL η (hblocks η))
    (norm_sum_ordinalSpaceBlockExtensions_le (𝕜 := 𝕜) L hL hblocks) x).map ev ev.continuous
  change HasSum (fun η => ordinalSpaceBlockExtension (𝕜 := 𝕜) L hL η (hblocks η) (x η) p.val)
    (ordinalSpaceBlocksSynthesis (𝕜 := 𝕜) L hL hblocks x p.val) at hs
  have hz (η : Set.Iio γ) (hη : η ≠ ξ) :
      ordinalSpaceBlockExtension (𝕜 := 𝕜) L hL η (hblocks η) (x η) p.val = 0 := by
    apply ordinalSpaceBlockExtension_apply_of_not_mem
    intro hp
    exact Set.disjoint_left.mp (ordinalSpaceBlocks_pairwiseDisjoint L hL hη) hp p.prop
  have ht : (∑' η, ordinalSpaceBlockExtension (𝕜 := 𝕜) L hL η (hblocks η) (x η) p.val) =
      ordinalSpaceBlockExtension (𝕜 := 𝕜) L hL ξ (hblocks ξ) (x ξ) p.val := tsum_eq_single ξ hz
  rw [hs.tsum_eq] at ht
  exact ht.trans (ordinalSpaceBlockExtension_apply_point L hL ξ (hblocks ξ) (x ξ) z)

@[simp] theorem ordinalSpaceKernelCoordinates_synthesis
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)
    (x : CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ))) :
    ordinalSpaceKernelCoordinates (𝕜 := 𝕜) L hL hzero htop hblocks
      (ordinalSpaceBlocksKernelSynthesis (𝕜 := 𝕜) L hL hblocks x) = x := by
  apply CZeroSum.ext
  intro ξ
  apply Subtype.ext
  ext z
  exact ordinalSpaceBlocksSynthesis_apply_point L hL hblocks x ξ z

/-- Kislyakov (3.1), for the actual kernel including the isolated initial point. -/
def ordinalSpaceRestrictionKernelBlockIsometry
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) L) ≃ₗᵢ[𝕜]
      CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)) :=
  LinearIsometryEquiv.ofSurjective
    (ordinalSpaceKernelCoordinatesIsometry (𝕜 := 𝕜) L hL hzero htop hblocks)
    (fun x => ⟨ordinalSpaceBlocksKernelSynthesis (𝕜 := 𝕜) L hL hblocks x,
      ordinalSpaceKernelCoordinates_synthesis L hL hzero htop hblocks x⟩)

end JLMS

