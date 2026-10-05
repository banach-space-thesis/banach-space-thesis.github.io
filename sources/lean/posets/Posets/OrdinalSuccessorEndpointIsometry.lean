import Posets.OrdinalRegularOmegaAssemblyEndpoint
import Posets.CombinedSpaces
import JLMS.CompactCZeroEquiv

/-! Zero endpoint functions at a successor are precisely the continuous
functions on its compact predecessor interval, with the same norm. -/

noncomputable section
open Set Topology
universe u
namespace Posets

variable {𝕜 : Type} [RCLike 𝕜]

def ordinalSuccessorHalfOpenHomeomorph (α : Ordinal.{u}) :
    Iio (Order.succ α) ≃ₜ JLMS.OrdinalInterval α :=
  Homeomorph.setCongr (by ext x; simp [JLMS.OrdinalInterval])

def ordinalSuccessorEndpointIsometry (α : Ordinal.{u}) :
    JLMS.ordinalEndpointZero 𝕜 (Order.succ α) ≃ₗᵢ[𝕜] JLMS.OrdinalC 𝕜 α :=
  (ordinalEndpointCZeroIsometry (𝕜 := 𝕜) (Order.succ α)).trans
    ((ThesisCommon.cZeroHomeomorphIsometryEquiv (ordinalSuccessorHalfOpenHomeomorph α).symm).trans
      (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := JLMS.OrdinalInterval α)).symm)

end Posets
