import Posets.SzlenkDirac
import Posets.TopologyStatements
import ThesisCommon.Analysis.OrdinalBakerPowers
import ThesisCommon.Analysis.OrdinalBakerDerived

/-! The two strict Szlenk lower bounds required in Proposition 3.4. -/

noncomputable section
open Set ThesisCommon
open scoped Ordinal
namespace Posets

theorem ordinalInterval_power_ordinalDerived_nonempty (α : Ordinal.{0}) (hα : α ≠ 0) :
    (ordinalDerived (univ : Set (OrdinalInterval (ω ^ α))) α).Nonempty := by
  have hIcc : Icc (0 : Ordinal.{0}) (ω ^ α) = Iic (ω ^ α) := by ext x; simp
  have h := ordinalDerived_image_closedEmbedding
    (isClosed_Icc : IsClosed (Icc (0 : Ordinal.{0}) (ω ^ α))).isClosedEmbedding_subtypeVal
    univ α
  rw [image_univ, Subtype.range_coe] at h
  have hi : ordinalDerived (Iic (ω ^ α)) α =
      (Subtype.val : OrdinalInterval (ω ^ α) → Ordinal.{0}) '' ordinalDerived univ α := by
    calc
      ordinalDerived (Iic (ω ^ α)) α = ordinalDerived (Icc (0 : Ordinal.{0}) (ω ^ α)) α :=
        congrArg (fun S => ordinalDerived S α) hIcc.symm
      _ = _ := h
  rw [ordinalDerived_Iic_power_self hα] at hi
  have hn : ((Subtype.val : OrdinalInterval (ω ^ α) → Ordinal.{0}) ''
      ordinalDerived univ α).Nonempty := by
    rw [← hi]
    exact singleton_nonempty _
  exact Set.Nonempty.of_image hn

theorem ordinalPower_not_operatorSzlenkBound (𝕜 : Type) [RCLike 𝕜]
    (α : Ordinal.{0}) (hα : α ≠ 0) :
    ¬ OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (OrdinalSpace 𝕜 (ω ^ α))) α :=
  not_operatorSzlenkBound_id_of_ordinalDerived_nonempty
    (ordinalInterval_power_ordinalDerived_nonempty α hα)

theorem ordinalOmegaOmega_not_szlenkBound_omega (𝕜 : Type) [RCLike 𝕜] :
    ¬ OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (OrdinalSpace 𝕜 (ω ^ ω))) (ω : Ordinal.{0}) :=
  ordinalPower_not_operatorSzlenkBound 𝕜 ω Ordinal.omega0_ne_zero

theorem ordinalOmegaOmegaSq_not_szlenkBound_omegaSq (𝕜 : Type) [RCLike 𝕜] :
    ¬ OperatorSzlenkBound
      (ContinuousLinearMap.id 𝕜 (OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))))) (ω ^ (2 : Ordinal.{0})) :=
  ordinalPower_not_operatorSzlenkBound 𝕜 _ (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)

end Posets
