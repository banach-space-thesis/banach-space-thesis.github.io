import JLMS.OrdinalProjectionCopies
import JLMS.LoyWillisDecomposition

/-!
# Ogden Proposition 6.17: the endpoint-column operator

An endpoint-column rank-one operator whose endpoint entry is zero is fixed
on the left by some head projection. The constant-tail theorem supplies the
cutoff, and the head projection belongs to every continuity ideal.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] ordinalProjectionFunctionGroup ordinalProjectionFunctionSpace
  ordinalProjectionOperatorGroup ordinalProjectionOperatorSpace ordinalProjectionOperatorAlgebra
  ordinalProjectionOperatorScalarTower ordinalProjectionOperatorScalarComm

theorem ordinalHeadProjection_mul_endpointRankOne (α β : Ordinal.{u}) (f : OrdinalC 𝕜 α) :
    ordinalHeadProjection α β * ordinalEndpointRankOne α f =
      ordinalEndpointRankOne α (ordinalHeadProjection α β f) := by
  apply ContinuousLinearMap.ext
  intro g
  change ordinalHeadProjection α β (g ⟨α, Ordinal.zero_le _, le_rfl⟩ • f) =
    g ⟨α, Ordinal.zero_le _, le_rfl⟩ • ordinalHeadProjection α β f
  exact map_smul _ _ _

theorem ogden_endpointRankOne_mem_continuityIdeal
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (θ : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₙₐ[𝕜] A)
    (f : OrdinalC 𝕜 c.ord) (hf : f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) :
    ordinalEndpointRankOne c.ord f ∈
      continuityIdeal (𝕜 := 𝕜) (B := OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (A := A) θ := by
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  obtain ⟨β, hβ, hfix⟩ := exists_ordinalHeadProjection_fixes_zeroEndpoint hcf f hf
  have hJ := initialOrdinalHeadProjection_mem_continuityIdeal hu.le hβ θ
  have hm := continuityIdeal_mul_right θ (ordinalEndpointRankOne c.ord f) hJ
  simpa only [ordinalHeadProjection_mul_endpointRankOne, hfix] using hm

end JLMS
