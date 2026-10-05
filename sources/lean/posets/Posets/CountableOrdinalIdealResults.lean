import Posets.CountableOrdinalIdealReduction
import Posets.CountableOrdinalPFPCanonical

/-! The countable-ordinal primary factorisation theorem and the exact
compact-metric ideal corollary of the paper. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]

theorem countableOrdinal_hasPFP (α : Ordinal.{0})
    (hcα : α.card ≤ Cardinal.aleph0) (hα : Ordinal.omega0 ≤ α) :
    HasPFP 𝕜 (OrdinalSpace 𝕜 α) :=
  countableOrdinal_hasPFP_of_canonical countableCanonicalOrdinal_hasPFP α hcα hα

/-- Proposition 3.1 for every countable ordinal; the uncountable case is
separate and is not asserted by this declaration. -/
theorem proposition_3_1_countable (α : Ordinal.{0})
    (hcα : α.card ≤ Cardinal.aleph0) : Proposition_3_1 𝕜 α := by
  intro hα
  exact proposition_3_1_of_ordinal_hasPFP α (countableOrdinal_hasPFP α hcα hα) hα

/-- Corollary 3.3, with the author's nonempty-space convention explicit
in the original formal target. -/
theorem corollary_3_3 : Corollary_3_3 𝕜 :=
  corollary_3_3_of_countable_ordinal_hasPFP countableOrdinal_hasPFP

theorem ordinalOmegaOmegaSq_hasPFP :
    HasPFP 𝕜 (OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal.{0})))) :=
  countableCanonicalOrdinal_hasPFP 2 (by simpa using (Cardinal.nat_lt_aleph0 2).le)

end Posets
