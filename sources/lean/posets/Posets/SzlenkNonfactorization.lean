import Posets.SzlenkClosedIdeals
import Posets.SzlenkDiracOrdinal

/-! An identity with larger Szlenk index cannot factor through an operator
in a smaller Szlenk class. This implication needs no maximal-ideal theorem. -/

noncomputable section
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem OperatorSzlenkBound.doesNotFactorIdentity {T : E →L[𝕜] E} {α : Ordinal}
    (hT : OperatorSzlenkBound T α)
    (hF : ¬ OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 F) α) :
    DoesNotFactorIdentity 𝕜 T F := by
  rintro ⟨A, B, hAB⟩
  exact hF (hAB ▸ hT.comp A B)

theorem ordinalOmegaOmegaSq_szlenk_two_subset_nonfactorization :
    SzlenkOperatorClass (𝕜 := 𝕜)
      (E := OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal))))
      (F := OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal))))
      (2 : Ordinal.{0}) ⊆
    {T | DoesNotFactorIdentity 𝕜 T
      (OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal))))} := by
  intro T hT
  exact hT.doesNotFactorIdentity (ordinalOmegaOmegaSq_not_szlenkBound_omegaSq 𝕜)

end Posets
