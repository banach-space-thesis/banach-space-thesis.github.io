import Posets.SzlenkNormClosed
import Posets.SzlenkIdealAddition
import Posets.SzlenkOrdinalNaturalSum
import PosetsCommon.Algebra

/-! The closed two-sided Szlenk ideals actually used in Proposition 3.4. -/

noncomputable section
universe v
open scoped Ordinal NaturalOps
namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem isClosedIdeal_operatorSzlenkBound (κ : Ordinal) (hκpos : 1 ≤ κ)
    (hκ : ∀ a < κ, ∀ b < κ, a ♯ b < κ) :
    ThesisCommon.IsClosedIdeal 𝕜 {T : E →L[𝕜] E | OperatorSzlenkBound T κ} := by
  refine ⟨isClosed_operatorSzlenkBound κ, operatorSzlenkBound_zero hκpos,
    ?_, ?_, ?_⟩
  · intro S hS T hT
    exact hS.add hκ hT
  · intro c T hT
    exact hT.smul c
  · intro S T hT
    exact ⟨hT.postcomp S, hT.precomp S⟩

theorem isClosedIdeal_szlenk_one :
    ThesisCommon.IsClosedIdeal 𝕜 (SzlenkOperatorClass (𝕜 := 𝕜) (E := E) (F := E) (1 : Ordinal.{v})) := by
  simpa only [SzlenkOperatorClass, Ordinal.opow_one] using
    isClosedIdeal_operatorSzlenkBound (𝕜 := 𝕜) (E := E) ω Ordinal.one_lt_omega0.le
      (fun a ha b hb => nadd_lt_omega0 ha hb)

theorem isClosedIdeal_szlenk_two :
    ThesisCommon.IsClosedIdeal 𝕜 (SzlenkOperatorClass (𝕜 := 𝕜) (E := E) (F := E) (2 : Ordinal.{v})) := by
  exact isClosedIdeal_operatorSzlenkBound (𝕜 := 𝕜) (E := E) (ω ^ (2 : Ordinal.{v}))
    (Order.one_le_iff_pos.mpr (Ordinal.opow_pos _ Ordinal.omega0_pos))
    (fun a ha b hb => nadd_lt_omega0_sq ha hb)

theorem szlenk_one_subset_two :
    SzlenkOperatorClass (𝕜 := 𝕜) (E := E) (F := E) (1 : Ordinal.{v}) ⊆
      SzlenkOperatorClass (2 : Ordinal.{v}) := by
  intro T hT
  change OperatorSzlenkBound T (ω ^ (2 : Ordinal.{v}))
  exact hT.mono (Ordinal.opow_le_opow_right Ordinal.omega0_pos
    (show (1 : Ordinal.{v}) ≤ 2 by norm_num))

end Posets
