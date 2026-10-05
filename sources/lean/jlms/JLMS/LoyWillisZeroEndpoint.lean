import JLMS.LoyWillisAlgebra
import JLMS.LoyWillisDecomposition
import JLMS.CodimensionTwoContinuity
import JLMS.NullSequenceContinuity

/-!
# Ogden's subspace M₀ and extension from its restriction

M₀ consists of operators in M whose endpoint diagonal entry is zero. The
identity and the constant endpoint rank-one operator supply its two missing
scalar directions. Continuity on M₀ therefore implies continuity everywhere.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)

local instance loyWillisZeroOperatorGroup : NormedAddCommGroup
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance
local instance loyWillisZeroOperatorSpace : NormedSpace 𝕜
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance

def loyWillisZeroEndpointSubspace : Submodule 𝕜
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :=
  loyWillisSubspace hc hu ⊓ LinearMap.ker (ordinalEndpointCoefficient (𝕜 := 𝕜) c.ord)

theorem mem_loyWillisZeroEndpointSubspace_iff
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    T ∈ loyWillisZeroEndpointSubspace hc hu ↔ T ∈ loyWillisSubspace hc hu ∧
      ordinalEndpointCoefficient (𝕜 := 𝕜) c.ord T = 0 := Iff.rfl

theorem continuous_of_continuous_on_loyWillisZeroEndpoint
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₗ[𝕜] F)
    (hf : Continuous (f.comp (loyWillisZeroEndpointSubspace hc hu).subtype)) :
    Continuous f := by
  let r : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    ordinalEndpointRankOne c.ord (ContinuousMap.const _ 1)
  have hrM : r ∈ loyWillisSubspace hc hu :=
    ordinalEndpointRankOne_mem_loyWillisSubspace hc hu _
  have hχr : initialEndpointJump (𝕜 := 𝕜) hc hu r = 0 := hrM
  have hψr : ordinalEndpointCoefficient (𝕜 := 𝕜) c.ord r = 1 := by
    simp [r, ordinalEndpointCoefficient_apply]
  exact continuous_of_continuous_on_two_kernels f (initialEndpointJump hc hu)
    (ordinalEndpointCoefficient c.ord) (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)) r
      (initialEndpointJump_id hc hu) hχr hψr hf

end JLMS
