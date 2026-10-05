import JLMS.OrdinalSpaceBlocksEquiv
import JLMS.OrdinalSpaceRetractionBounded

/-!
# Kislyakov's block decomposition with uniform bounds

The ceiling retraction and the isometric kernel coordinates give the actual
product decompositions. Both directions have norm at most two, independently
of the ordinal embedding and the block lengths, as needed for c₀ sums.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}
attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace
  ordinalRestrictionKernelGroup ordinalRestrictionKernelSpace

variable (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
  (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
  (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
  (hblocks : ∀ ξ, Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ)

def ordinalSpaceBlocksEquiv :
    OrdinalC 𝕜 β ≃L[𝕜] OrdinalC 𝕜 γ ×
      CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)) :=
  (ordinalSpaceRetractionEquiv (𝕜 := 𝕜) L hL htop).trans
    ((ContinuousLinearEquiv.refl 𝕜 (OrdinalC 𝕜 γ)).prodCongr
      (ordinalSpaceRestrictionKernelBlockIsometry (𝕜 := 𝕜) L hL hzero htop hblocks).toContinuousLinearEquiv)

def ordinalEndpointZeroBlocksEquiv :
    ordinalEndpointZero 𝕜 β ≃L[𝕜] ordinalEndpointZero 𝕜 γ ×
      CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)) :=
  (ordinalEndpointZeroRetractionEquiv (𝕜 := 𝕜) L hL htop).trans
    ((ContinuousLinearEquiv.refl 𝕜 (ordinalEndpointZero 𝕜 γ)).prodCongr
      (ordinalSpaceRestrictionKernelBlockIsometry (𝕜 := 𝕜) L hL hzero htop hblocks).toContinuousLinearEquiv)

theorem norm_ordinalSpaceBlocksEquiv_apply_le (f : OrdinalC 𝕜 β) :
    ‖ordinalSpaceBlocksEquiv (𝕜 := 𝕜) L hL hzero htop hblocks f‖ ≤ 2 * ‖f‖ := by
  let e := ordinalSpaceRestrictionKernelBlockIsometry (𝕜 := 𝕜) L hL hzero htop hblocks
  change max ‖(ordinalSpaceRetractionEquiv (𝕜 := 𝕜) L hL htop f).1‖
    ‖e (ordinalSpaceRetractionEquiv (𝕜 := 𝕜) L hL htop f).2‖ ≤ 2 * ‖f‖
  rw [e.norm_map]
  exact norm_ordinalSpaceRetractionEquiv_apply_le L hL htop f

theorem norm_ordinalSpaceBlocksEquiv_symm_apply_le
    (y : OrdinalC 𝕜 γ ×
      CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ))) :
    ‖(ordinalSpaceBlocksEquiv (𝕜 := 𝕜) L hL hzero htop hblocks).symm y‖ ≤ 2 * ‖y‖ := by
  let e := ordinalSpaceRestrictionKernelBlockIsometry (𝕜 := 𝕜) L hL hzero htop hblocks
  change ‖(ordinalSpaceRetractionEquiv (𝕜 := 𝕜) L hL htop).symm (y.1, e.symm y.2)‖ ≤ 2 * ‖y‖
  calc
    _ ≤ 2 * ‖(y.1, e.symm y.2)‖ := norm_ordinalSpaceRetractionEquiv_symm_apply_le L hL htop _
    _ = 2 * ‖y‖ := by simp only [Prod.norm_def, e.symm.norm_map]

theorem norm_ordinalEndpointZeroBlocksEquiv_apply_le (f : ordinalEndpointZero 𝕜 β) :
    ‖ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜) L hL hzero htop hblocks f‖ ≤ 2 * ‖f‖ := by
  let e := ordinalSpaceRestrictionKernelBlockIsometry (𝕜 := 𝕜) L hL hzero htop hblocks
  change max ‖(ordinalEndpointZeroRetractionEquiv (𝕜 := 𝕜) L hL htop f).1‖
    ‖e (ordinalEndpointZeroRetractionEquiv (𝕜 := 𝕜) L hL htop f).2‖ ≤ 2 * ‖f‖
  rw [e.norm_map]
  exact norm_ordinalEndpointZeroRetractionEquiv_apply_le L hL htop f

theorem norm_ordinalEndpointZeroBlocksEquiv_symm_apply_le
    (y : ordinalEndpointZero 𝕜 γ ×
      CZeroSum 𝕜 (fun ξ : Set.Iio γ => ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ))) :
    ‖(ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜) L hL hzero htop hblocks).symm y‖ ≤ 2 * ‖y‖ := by
  let e := ordinalSpaceRestrictionKernelBlockIsometry (𝕜 := 𝕜) L hL hzero htop hblocks
  change ‖(ordinalEndpointZeroRetractionEquiv (𝕜 := 𝕜) L hL htop).symm (y.1, e.symm y.2)‖ ≤ 2 * ‖y‖
  calc
    _ ≤ 2 * ‖(y.1, e.symm y.2)‖ :=
      norm_ordinalEndpointZeroRetractionEquiv_symm_apply_le L hL htop _
    _ = 2 * ‖y‖ := by simp only [Prod.norm_def, e.symm.norm_map]

end JLMS

