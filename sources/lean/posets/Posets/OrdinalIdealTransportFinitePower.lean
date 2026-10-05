import Posets.OrdinalIdealTransport
import Posets.MatrixIdealTransportOperators
import Posets.TopologyStatements
import JLMS.OrdinalSpaceFinitePower

/-! The actual finite-multiple decomposition transfers maximal operator ideals. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]

set_option synthInstance.maxSize 4096 in
theorem uniqueMaximalClosed_ordinal_finiteMultiple_iff
    (α : Ordinal.{0}) (hα : Ordinal.omega0 ≤ α) (n : ℕ) :
    HasUniqueMaximalClosedIdeal 𝕜
        (OrdinalSpace 𝕜 (α * ((n+1 : ℕ) : Ordinal)) →L[𝕜]
          OrdinalSpace 𝕜 (α * ((n+1 : ℕ) : Ordinal))) ↔
      HasUniqueMaximalClosedIdeal 𝕜 (OrdinalSpace 𝕜 α →L[𝕜] OrdinalSpace 𝕜 α) :=
  (uniqueMaximalClosed_operator_equiv (JLMS.ordinalSpaceFinitePower (𝕜 := 𝕜) α hα n)).trans
    (uniqueMaximalClosed_finitePower_iff (𝕜 := 𝕜) (E := OrdinalSpace 𝕜 α)
      (ι := Fin (n+1)))

end Posets
