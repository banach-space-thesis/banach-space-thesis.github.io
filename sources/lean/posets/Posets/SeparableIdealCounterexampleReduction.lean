import Posets.SzlenkFourIdeals
import Posets.SeparableMissingIdealCount

/-! Exact assembly of Proposition 3.4 from its two remaining analytic inputs.
The hypotheses explicitly name the primary factorisation theorem and the
surjective counterexample; this is a conditional result, not a full proof. -/

noncomputable section
open ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem proposition_3_4_of_counterexample
    (hpfp : HasPFP 𝕜 (OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0})))))
    (T : OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) →L[𝕜]
      OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))))
    (hT : Function.Surjective T)
    (hTn : DoesNotFactorIdentity 𝕜 T (OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))))) :
    Proposition_3_4 𝕜 := by
  have h4 := ordinalOmegaOmegaSq_four_ideals_of_counterexample hpfp T hT hTn
  exact ⟨h4, missingSeparableIdealCount_of_four_ordinalIdeals h4⟩

end Posets
