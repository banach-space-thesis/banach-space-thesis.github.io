import Posets.OrdinalIdealTransportFinitePower
import Posets.NonfactorizationIdeal
import JLMS.OrdinalSpaceOmega
import ThesisCommon.Analysis.CountableOnePointPrimariness

/-! The actual primary-factorisation base case for the ordinal interval [0,ω]. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]

/-- The common primary-factorisation vocabulary implies the paper's literal
identity-factorisation criterion, with the factors in their specified order. -/
theorem uniqueMaximal_of_hasPFP {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] [Nontrivial E] (h : HasPFP 𝕜 E) :
    IsMaximalClosedIdeal 𝕜 {T : E →L[𝕜] E | DoesNotFactorIdentity 𝕜 T E} ∧
      HasUniqueMaximalClosedIdeal 𝕜 (E →L[𝕜] E) := by
  apply uniqueMaximal_of_identity_split
  intro T
  rcases h T with ⟨U, V, hUV⟩ | ⟨U, V, hUV⟩
  · exact Or.inl ⟨V, U, by simpa only [ContinuousLinearMap.comp_assoc] using hUV⟩
  · exact Or.inr ⟨V, U, by simpa only [ContinuousLinearMap.comp_assoc] using hUV⟩

def ordinalOmegaCZeroEquiv : OrdinalSpace 𝕜 Ordinal.omega0 ≃L[𝕜] CZeroSum 𝕜 :=
  (continuousMapHomeomorphEquiv JLMS.ordinalOmegaOnePointHomeomorph.symm).trans
    onePointContinuousCZeroEquiv

theorem ordinalOmega_hasUPFP : HasUPFP 𝕜 (OrdinalSpace 𝕜 Ordinal.omega0) :=
  scalar_cZero_hasUPFP.of_equiv ordinalOmegaCZeroEquiv.symm

/-- Both conclusions of Proposition 3.1 hold at the first infinite ordinal;
the nonfactorisation ideal is maximal without any exceptional-case hypothesis. -/
theorem proposition_3_1_omega : Proposition_3_1 𝕜 Ordinal.omega0 := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) Ordinal.omega0) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (𝕜 := 𝕜) (ordinalOmega_hasUPFP (𝕜 := 𝕜)).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets



