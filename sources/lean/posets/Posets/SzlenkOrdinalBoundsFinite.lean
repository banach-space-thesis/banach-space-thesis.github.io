import Posets.SzlenkOrdinalBoundsCZero
import Posets.OrdinalIdealTransportCountablePowers

/-! Actual Szlenk upper bounds for finite positive ordinal powers. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]

theorem OperatorSzlenkBound.id_of_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {α : Ordinal} (h : OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 F) α)
    (e : E ≃L[𝕜] F) : OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 E) α := by
  have hh := (h.precomp e.toContinuousLinearMap).postcomp e.symm.toContinuousLinearMap
  have he : e.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id 𝕜 F).comp e.toContinuousLinearMap) =
      ContinuousLinearMap.id 𝕜 E := by ext x; exact e.symm_apply_apply x
  rwa [he] at hh

theorem ordinalFinitePower_szlenkBound_omega0 (n : ℕ) :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜
      (OrdinalSpace 𝕜 (Ordinal.omega0 ^ ((n + 1 : ℕ) : Ordinal.{0})))) Ordinal.omega0 :=
  cZero_szlenkBound_omega0.id_of_equiv (ordinalFinitePowerCZeroEquiv n)

end Posets
