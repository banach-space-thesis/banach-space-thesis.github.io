import Posets.OrdinalPrincipalUncountablePreservation
import Posets.OrdinalFinalClassificationReduction

/-! The exact Proposition 3.1, with all principal-preservation inputs proved. -/

noncomputable section
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem proposition_3_1_proof (α : Ordinal.{0}) : Proposition_3_1 𝕜 α :=
  proposition_3_1_of_principal_preservation ordinalPrincipal_hasUPFP α

end Posets

