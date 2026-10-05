import JLMS.OrdinalSpaceRetraction

/-!
# Uniform bounds for the ordinal retraction decomposition

Restriction is contractive and ceiling extension is isometric. Both the
product decomposition and its inverse have norm at most two, uniformly in
the ordinals and in the chosen cofinal embedding. The same constants hold
for the endpoint-zero decomposition, so these maps can be used in c₀ sums.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace
  ordinalRestrictionKernelGroup ordinalRestrictionKernelSpace

theorem norm_ordinalSpaceRestriction_apply_le {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (f : OrdinalC 𝕜 β) :
    ‖ordinalSpaceRestriction g f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm (g x))

theorem norm_ordinalSpaceRestriction_le {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) :
    ‖ordinalSpaceRestriction (𝕜 := 𝕜) g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_ordinalSpaceRestriction_apply_le g f

theorem norm_ordinalSpaceCeilingExtension_apply {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 γ) : ‖ordinalSpaceCeilingExtension g hg htop f‖ = ‖f‖ := by
  apply le_antisymm (norm_ordinalSpaceRestriction_apply_le _ f)
  have h := norm_ordinalSpaceRestriction_apply_le g (ordinalSpaceCeilingExtension g hg htop f)
  rwa [ordinalSpaceRestriction_ceilingExtension] at h

theorem norm_ordinalSpaceCeilingExtension_le {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    ‖ordinalSpaceCeilingExtension (𝕜 := 𝕜) g hg htop‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [norm_ordinalSpaceCeilingExtension_apply, one_mul]

theorem norm_ordinalSpaceRetractionEquiv_apply_le {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 β) : ‖ordinalSpaceRetractionEquiv g hg htop f‖ ≤ 2 * ‖f‖ := by
  change max ‖ordinalSpaceRestriction g f‖
    ‖f - ordinalSpaceCeilingExtension g hg htop (ordinalSpaceRestriction g f)‖ ≤ 2 * ‖f‖
  apply max_le
  · exact (norm_ordinalSpaceRestriction_apply_le g f).trans (by nlinarith [norm_nonneg f])
  · calc
      ‖f - ordinalSpaceCeilingExtension g hg htop (ordinalSpaceRestriction g f)‖ ≤
          ‖f‖ + ‖ordinalSpaceCeilingExtension g hg htop (ordinalSpaceRestriction g f)‖ :=
        norm_sub_le _ _
      _ = ‖f‖ + ‖ordinalSpaceRestriction g f‖ := by rw [norm_ordinalSpaceCeilingExtension_apply]
      _ ≤ ‖f‖ + ‖f‖ := add_le_add_left (norm_ordinalSpaceRestriction_apply_le g f) _
      _ = 2 * ‖f‖ := (two_mul _).symm

theorem norm_ordinalSpaceRetractionEquiv_symm_apply_le {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (y : OrdinalC 𝕜 γ × LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) g)) :
    ‖(ordinalSpaceRetractionEquiv g hg htop).symm y‖ ≤ 2 * ‖y‖ := by
  change ‖ordinalSpaceCeilingExtension g hg htop y.1 + y.2.val‖ ≤ 2 * ‖y‖
  calc
    ‖ordinalSpaceCeilingExtension g hg htop y.1 + y.2.val‖ ≤
        ‖ordinalSpaceCeilingExtension g hg htop y.1‖ + ‖y.2.val‖ := norm_add_le _ _
    _ = ‖y.1‖ + ‖y.2‖ := by rw [norm_ordinalSpaceCeilingExtension_apply]; rfl
    _ ≤ ‖y‖ + ‖y‖ := add_le_add (le_max_left _ _) (le_max_right _ _)
    _ = 2 * ‖y‖ := (two_mul _).symm

theorem norm_ordinalEndpointZeroRetractionEquiv_apply_le {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : ordinalEndpointZero 𝕜 β) :
    ‖ordinalEndpointZeroRetractionEquiv g hg htop f‖ ≤ 2 * ‖f‖ := by
  change ‖ordinalSpaceRetractionEquiv g hg htop f.val‖ ≤ 2 * ‖f.val‖
  exact norm_ordinalSpaceRetractionEquiv_apply_le g hg htop f.val

theorem norm_ordinalEndpointZeroRetractionEquiv_symm_apply_le {γ β : Ordinal.{u}}
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (y : ordinalEndpointZero 𝕜 γ × LinearMap.ker (ordinalSpaceRestriction (𝕜 := 𝕜) g)) :
    ‖(ordinalEndpointZeroRetractionEquiv g hg htop).symm y‖ ≤ 2 * ‖y‖ := by
  change ‖(ordinalSpaceRetractionEquiv g hg htop).symm (y.1.val, y.2)‖ ≤
    2 * ‖(y.1.val, y.2)‖
  exact norm_ordinalSpaceRetractionEquiv_symm_apply_le g hg htop _

end JLMS
